/**
 * Reassignment analysis — determines which `let`-declared names are ever reassigned.
 * This determines whether a binding becomes `letConst` or `letMut` in JSCore₀.
 */

import { Node, SyntaxKind, FunctionDeclaration, ArrowFunction, MethodDeclaration } from "ts-morph";

/**
 * Walk a function body and build the set of `let`-declared names that are reassigned.
 */
export function findReassignedVars(
  body: Node
): Set<string> {
  const reassigned = new Set<string>();
  walkForReassignments(body, reassigned);
  return reassigned;
}

function walkForReassignments(node: Node, reassigned: Set<string>): void {
  // Binary expression with = operator (assignment)
  if (node.getKind() === SyntaxKind.BinaryExpression) {
    const binary = node;
    const children = binary.getChildren();
    // children[1] is the operator token
    if (children.length >= 3) {
      const opToken = children[1];
      if (opToken.getKind() === SyntaxKind.EqualsToken) {
        const left = children[0];
        if (left.getKind() === SyntaxKind.Identifier) {
          reassigned.add(left.getText());
        }
      }
      // Also handle +=, -=, etc.
      const compoundOps = [
        SyntaxKind.PlusEqualsToken,
        SyntaxKind.MinusEqualsToken,
        SyntaxKind.AsteriskEqualsToken,
        SyntaxKind.SlashEqualsToken,
        SyntaxKind.PercentEqualsToken,
      ];
      if (compoundOps.includes(opToken.getKind())) {
        const left = children[0];
        if (left.getKind() === SyntaxKind.Identifier) {
          reassigned.add(left.getText());
        }
      }
    }
  }

  // Prefix/Postfix ++ and --
  if (
    node.getKind() === SyntaxKind.PrefixUnaryExpression ||
    node.getKind() === SyntaxKind.PostfixUnaryExpression
  ) {
    const children = node.getChildren();
    for (const child of children) {
      if (child.getKind() === SyntaxKind.Identifier) {
        reassigned.add(child.getText());
      }
    }
  }

  // Don't recurse into nested function declarations/arrows
  if (
    node.getKind() === SyntaxKind.FunctionDeclaration ||
    node.getKind() === SyntaxKind.ArrowFunction ||
    node.getKind() === SyntaxKind.FunctionExpression
  ) {
    return;
  }

  for (const child of node.getChildren()) {
    walkForReassignments(child, reassigned);
  }
}

/**
 * Check if a variable declaration uses `let` (not `const`).
 */
export function isLetDeclaration(node: Node): boolean {
  if (node.getKind() === SyntaxKind.VariableDeclarationList) {
    const text = node.getText();
    return text.startsWith("let ");
  }
  return false;
}
