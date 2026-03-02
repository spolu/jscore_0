/**
 * Lean Theorem Generator — Annotations → theorem statements.
 * For each @invariant: generate `theorem fn_tag ... := by sorry`
 * @requires → hypotheses, @ensures → nested under ∃ fields with TS type predicate
 */

import { RequiresAnnotation, InvariantAnnotation } from "./annotation-parser";

/**
 * Generate a Lean theorem statement from an invariant annotation.
 */
export function generateTheorem(
  functionName: string,
  invariant: InvariantAnnotation,
  requires: RequiresAnnotation[],
  params: string[],
  tagIndex: number = 0
): string {
  const tag = sanitizeTag(invariant.tag);
  const thmName = tagIndex > 0 ? `${functionName}_${tag}_${tagIndex}` : `${functionName}_${tag}`;

  const lines: string[] = [];
  lines.push(`theorem ${thmName}`);

  // Universal quantifiers for fuel and params
  lines.push(`    (fuel : Nat)`);
  for (const param of params) {
    lines.push(`    (${param} : Val)`);
  }

  // Build env from params
  lines.push(`    (env : Env)`);
  lines.push(`    (store : Store)`);

  // @requires become hypotheses
  for (let i = 0; i < requires.length; i++) {
    const req = requires[i];
    const leanProp = translatePropertyToLean(req.prop, params);
    lines.push(`    (h_req_${i} : ${leanProp})`);
  }

  // The env binds all params
  const envSetup = params
    .map((p) => `env.set "${p}" ${p}`)
    .reduceRight((acc, set) => `(${set} |> fun e => ${acc})`, "env");

  // Generate the conclusion based on the invariant property
  const conclusion = translateInvariantToLean(
    invariant.prop,
    functionName,
    params
  );

  lines.push(`    : ${conclusion} := by`);
  lines.push(`  sorry`);

  return lines.join("\n");
}

/**
 * Translate a property from the annotation grammar to Lean.
 */
function translatePropertyToLean(prop: string, params: string[]): string {
  // Simple translations
  prop = prop.trim();

  // x > 0 → (∃ n, x = Val.num n ∧ n > 0)
  const compMatch = prop.match(
    /^(\w+(?:\.\w+)*)\s*(>|<|≥|≤|=|≠)\s*(.+)$/
  );
  if (compMatch) {
    const [, left, op, right] = compMatch;
    const leanOp = translateOp(op);

    // Check if comparing to a number
    if (/^\d+$/.test(right.trim())) {
      return `∃ n, ${translateAccess(left, params)} = some (Val.num n) ∧ n ${leanOp} ${right.trim()}`;
    }

    // Comparing two params
    return `${translateAccess(left, params)} ${leanOp} ${translateAccess(right.trim(), params)}`;
  }

  // x ∈ [values]
  const memMatch = prop.match(/^(\w+(?:\.\w+)*)\s*∈\s*\[(.+)\]$/);
  if (memMatch) {
    const [, varName, values] = memMatch;
    const valList = values.split(",").map((v) => v.trim());
    const leanVals = valList
      .map((v) => {
        if (v.startsWith('"') && v.endsWith('"')) {
          return `Val.str ${v}`;
        }
        return `Val.str "${v}"`;
      })
      .join(", ");
    return `Val.mem' (${translateAccess(varName, params)}) [${leanVals}]`;
  }

  // x starts_with y
  const swMatch = prop.match(
    /^(\w+(?:\.\w+)*)\s+starts_with\s+(.+)$/
  );
  if (swMatch) {
    const [, left, right] = swMatch;
    return `Val.startsWith' (${translateAccess(left, params)}) (${translateAccess(right.trim(), params)})`;
  }

  // Fallback: return as comment
  return `True /- TODO: ${prop} -/`;
}

/**
 * Translate an invariant proposition to a Lean conclusion.
 */
function translateInvariantToLean(
  prop: string,
  functionName: string,
  params: string[]
): string {
  prop = prop.trim();

  // ∀ call <pattern> (c) => <pred>
  const forallMatch = prop.match(/^∀\s+call\s+(\S+)\s+\((\w+)\)\s*=>\s*(.+)$/s);
  if (forallMatch) {
    const [, pattern, bindVar, pred] = forallMatch;
    return `∀ ${bindVar} ∈ callsTo (eval fuel env store ${functionName}_body).trace "${pattern}",\n      ${translateCallPred(pred.trim(), bindVar, params)}`;
  }

  // ¬ ∃ call <pattern>
  const noCallMatch = prop.match(/^¬\s*∃\s+call\s+(\S+)/);
  if (noCallMatch) {
    const [, pattern] = noCallMatch;
    return `callsTo (eval fuel env store ${functionName}_body).trace "${pattern}" = []`;
  }

  // ¬ tainted <binding> in call <pattern>
  const taintMatch = prop.match(
    /^¬\s*tainted\s+(\w+)\s+in\s+call\s+(\S+)/
  );
  if (taintMatch) {
    const [, source, pattern] = taintMatch;
    return `notTaintedIn ${functionName}_body "${source}" "${pattern}" = true`;
  }

  return `True /- TODO: ${prop} -/`;
}

function translateCallPred(
  pred: string,
  callVar: string,
  params: string[]
): string {
  // c.where.workspaceId = auth.workspaceId
  const eqMatch = pred.match(
    /^(\w+(?:\.\w+)*)\s*(=|≠)\s*(\w+(?:\.\w+)*)$/
  );
  if (eqMatch) {
    const [, left, op, right] = eqMatch;
    const leanOp = op === "=" ? "=" : "≠";
    const leanLeft = left.startsWith(callVar + ".")
      ? `argAtPath ${callVar} "${left.slice(callVar.length + 1)}"`
      : translateAccess(left, params);
    const leanRight = right.startsWith(callVar + ".")
      ? `argAtPath ${callVar} "${right.slice(callVar.length + 1)}"`
      : `some ${translateAccess(right, params)}`;
    return `${leanLeft} ${leanOp} ${leanRight}`;
  }

  return `True /- TODO: ${pred} -/`;
}

function translateAccess(path: string, params: string[]): string {
  const parts = path.split(".");
  if (parts.length === 1) {
    if (params.includes(parts[0])) {
      return parts[0];
    }
    return `Val.str "${parts[0]}"`;
  }

  // a.b.c → field access
  return parts[0];
}

function translateOp(op: string): string {
  switch (op) {
    case ">":
      return ">";
    case "<":
      return "<";
    case "≥":
      return "≥";
    case "≤":
      return "≤";
    case "=":
      return "=";
    case "≠":
      return "≠";
    default:
      return "=";
  }
}

function sanitizeTag(tag: string): string {
  return tag.replace(/[^a-zA-Z0-9_]/g, "_").replace(/-/g, "_");
}
