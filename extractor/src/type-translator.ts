/**
 * Type Translator — TS types → Val predicates (Lean propositions).
 * Uses the TypeChecker to resolve types and translate them structurally.
 */

import { Type, TypeChecker, Node, Symbol as TsSymbol, ts } from "ts-morph";

/**
 * Translate a TypeScript type into a Lean Val predicate string.
 * The predicate takes a variable name and returns a Lean proposition.
 *
 * @param type - The TypeScript type to translate
 * @param checker - The TypeScript type checker
 * @param varName - The Lean variable name to predicate over
 * @param accessedFields - Set of field paths actually accessed in the function body
 * @param depth - Current recursion depth (prevents infinite expansion)
 */
export function translateType(
  type: Type,
  checker: TypeChecker,
  varName: string,
  accessedFields: Set<string> = new Set(),
  depth: number = 0
): string {
  if (depth > 5) {
    return `True`; // unconstrained at depth limit
  }

  const typeText = type.getText();

  // Primitive types
  if (type.isString() || type.isStringLiteral()) {
    if (type.isStringLiteral()) {
      return `${varName} = Val.str "${type.getLiteralValue()}"`;
    }
    return `∃ s, ${varName} = Val.str s`;
  }

  if (type.isNumber() || type.isNumberLiteral()) {
    if (type.isNumberLiteral()) {
      return `${varName} = Val.num ${type.getLiteralValue()}`;
    }
    return `∃ n, ${varName} = Val.num n`;
  }

  if (type.isBoolean() || type.isBooleanLiteral()) {
    return `∃ b, ${varName} = Val.bool b`;
  }

  if (type.isNull() || type.isUndefined()) {
    return `${varName} = Val.none`;
  }

  if (typeText === "void") {
    return `${varName} = Val.none`;
  }

  // Union types: T | null, T | undefined, string literal unions
  if (type.isUnion()) {
    const unionTypes = type.getUnionTypes();

    // Check for T | null / T | undefined pattern
    const nullTypes = unionTypes.filter(
      (t) => t.isNull() || t.isUndefined()
    );
    const nonNullTypes = unionTypes.filter(
      (t) => !t.isNull() && !t.isUndefined()
    );

    if (nullTypes.length > 0 && nonNullTypes.length === 1) {
      const innerPred = translateType(
        nonNullTypes[0],
        checker,
        varName,
        accessedFields,
        depth + 1
      );
      return `${varName} = Val.none ∨ (${innerPred})`;
    }

    // String literal union: "a" | "b" | "c"
    if (unionTypes.every((t) => t.isStringLiteral())) {
      const cases = unionTypes.map(
        (t) => `${varName} = Val.str "${t.getLiteralValue()}"`
      );
      return cases.join(" ∨ ");
    }

    // General union
    const cases = unionTypes.map((t) =>
      translateType(t, checker, varName, accessedFields, depth + 1)
    );
    return cases.join(" ∨ ");
  }

  // Intersection types: A & B
  if (type.isIntersection()) {
    const parts = type.getIntersectionTypes();
    const preds = parts.map((t) =>
      translateType(t, checker, varName, accessedFields, depth + 1)
    );
    return preds.join(" ∧ ");
  }

  // Array type: T[]
  if (type.isArray()) {
    const elemType = type.getArrayElementType();
    if (elemType) {
      const elemPred = translateType(
        elemType,
        checker,
        "e",
        accessedFields,
        depth + 1
      );
      return `∃ elems, ${varName} = Val.arr elems ∧ ∀ e ∈ elems, ${elemPred}`;
    }
    return `∃ elems, ${varName} = Val.arr elems`;
  }

  // Object types: { k1: T1, k2: T2, ... }
  if (type.isObject() || type.isInterface()) {
    const properties = type.getProperties();

    if (properties.length === 0) {
      return `∃ fields, ${varName} = Val.obj fields`;
    }

    // Only expand fields that are accessed in the function body
    const relevantProps = properties.filter((prop) => {
      if (accessedFields.size === 0) return true; // expand all if no info
      return accessedFields.has(prop.getName());
    });

    if (relevantProps.length === 0) {
      return `∃ fields, ${varName} = Val.obj fields`;
    }

    const fieldPreds = relevantProps.map((prop) => {
      const propType = prop.getValueDeclaration()
        ? checker.getTypeAtLocation(prop.getValueDeclaration()!)
        : undefined;

      const fieldVar = `__f_${prop.getName()}`;
      const isOptional = prop.isOptional();

      if (!propType) {
        if (isOptional) {
          return `(fieldLookup fields "${prop.getName()}" = Option.none ∨ ∃ ${fieldVar}, fieldLookup fields "${prop.getName()}" = some ${fieldVar})`;
        }
        return `∃ ${fieldVar}, fieldLookup fields "${prop.getName()}" = some ${fieldVar}`;
      }

      const innerPred = translateType(
        propType,
        checker,
        fieldVar,
        accessedFields,
        depth + 1
      );

      if (isOptional) {
        return `(fieldLookup fields "${prop.getName()}" = Option.none ∨ ∃ ${fieldVar}, fieldLookup fields "${prop.getName()}" = some ${fieldVar} ∧ ${innerPred})`;
      }

      return `∃ ${fieldVar}, fieldLookup fields "${prop.getName()}" = some ${fieldVar} ∧ ${innerPred}`;
    });

    return `∃ fields, ${varName} = Val.obj fields ∧ ${fieldPreds.join(" ∧ ")}`;
  }

  // Fallback: unconstrained
  return `True`;
}

/**
 * Collect the set of field paths accessed on a binding in a function body.
 */
export function collectAccessedFields(
  body: Node,
  bindingName: string
): Set<string> {
  const fields = new Set<string>();
  walkForFieldAccess(body, bindingName, "", fields);
  return fields;
}

function walkForFieldAccess(
  node: Node,
  bindingName: string,
  currentPath: string,
  fields: Set<string>
): void {
  if (node.getKind() === ts.SyntaxKind.PropertyAccessExpression) {
    const children = node.getChildren();
    if (children.length >= 3) {
      const obj = children[0];
      const prop = children[children.length - 1].getText();

      if (obj.getText() === bindingName || obj.getText() === currentPath) {
        const fullPath = currentPath ? `${currentPath}.${prop}` : prop;
        fields.add(prop);
        fields.add(fullPath);

        // Continue walking to find deeper access
        for (const child of node.getChildren()) {
          walkForFieldAccess(child, bindingName, fullPath, fields);
        }
        return;
      }
    }
  }

  for (const child of node.getChildren()) {
    walkForFieldAccess(child, bindingName, "", fields);
  }
}
