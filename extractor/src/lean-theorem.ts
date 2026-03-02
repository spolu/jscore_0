/**
 * Lean Theorem Generator — Annotations → theorem statements.
 *
 * Three invariant shapes:
 *   1. ¬ tainted X in call P  → notTaintedIn body "X" "P" = true       (native_decide)
 *   2. ¬ ∃ call P             → (callExprsIn body "P").length = 0       (native_decide)
 *   3. ∀ call P (c) => pred   → runtime trace property                  (sorry)
 */

import { RequiresAnnotation, InvariantAnnotation } from "./annotation-parser";

interface InvariantTranslation {
  conclusion: string;
  needsRuntime: boolean;
}

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
  const thmName =
    tagIndex > 0 ? `${functionName}_${tag}_${tagIndex}` : `${functionName}_${tag}`;

  const { conclusion, needsRuntime } = translateInvariantToLean(
    invariant.prop,
    functionName,
    params
  );

  if (!needsRuntime) {
    // Purely syntactic theorem — no fuel/env/store/params needed
    return [
      `theorem ${thmName}`,
      `    : ${conclusion} := by`,
      `  native_decide`,
    ].join("\n");
  }

  // Runtime theorem — needs fuel, env, store, params, env bindings
  const lines: string[] = [];
  lines.push(`theorem ${thmName}`);
  lines.push(`    (fuel : Nat)`);
  for (const param of params) {
    lines.push(`    (${param} : Val)`);
  }
  lines.push(`    (env : Env)`);
  lines.push(`    (store : Store)`);

  // Env binding hypotheses: env "param" = some param
  for (const param of params) {
    lines.push(`    (h_env_${param} : env "${param}" = some ${param})`);
  }

  lines.push(`    : ${conclusion} := by`);
  lines.push(`  sorry`);

  return lines.join("\n");
}

/**
 * Translate an invariant proposition to a Lean conclusion.
 * Returns the conclusion string and whether it needs runtime (eval) reasoning.
 */
function translateInvariantToLean(
  prop: string,
  functionName: string,
  params: string[]
): InvariantTranslation {
  prop = prop.trim();

  // ¬ tainted <binding> in call <pattern> → purely syntactic
  const taintMatch = prop.match(
    /^¬\s*tainted\s+(\w+)\s+in\s+call\s+(\S+)/
  );
  if (taintMatch) {
    const [, source, pattern] = taintMatch;
    return {
      conclusion: `notTaintedIn ${functionName}_body "${source}" "${pattern}" = true`,
      needsRuntime: false,
    };
  }

  // ¬ ∃ call <pattern> → purely syntactic (no matching call sites in AST)
  const noCallMatch = prop.match(/^¬\s*∃\s+call\s+(\S+)/);
  if (noCallMatch) {
    const [, pattern] = noCallMatch;
    return {
      conclusion: `(callExprsIn ${functionName}_body "${pattern}").length = 0`,
      needsRuntime: false,
    };
  }

  // ∀ call <pattern> (c) => <pred> → runtime trace property
  const forallMatch = prop.match(
    /^∀\s+call\s+(\S+)\s+\((\w+)\)\s*=>\s*(.+)$/s
  );
  if (forallMatch) {
    const [, pattern, bindVar, pred] = forallMatch;
    return {
      conclusion: `∀ ${bindVar} ∈ callsTo (eval fuel env store ${functionName}_body).trace "${pattern}",\n      ${translateCallPred(pred.trim(), bindVar, params)}`,
      needsRuntime: true,
    };
  }

  return {
    conclusion: `True /- TODO: ${prop} -/`,
    needsRuntime: true,
  };
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
      : translateAccessAsOption(right, params);
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
  return parts[0];
}

/**
 * Translate a dotted access to an Option Val expression.
 * auth.workspaceId → Val.field' auth "workspaceId"
 * For simple params, wraps in `some`.
 */
function translateAccessAsOption(path: string, params: string[]): string {
  const parts = path.split(".");
  if (parts.length === 1) {
    if (params.includes(parts[0])) {
      return `some ${parts[0]}`;
    }
    return `some (Val.str "${parts[0]}")`;
  }

  // a.b → field access on a Val
  const base = parts[0];
  const fieldPath = parts.slice(1);
  if (fieldPath.length === 1) {
    return `Val.field' ${base} "${fieldPath[0]}"`;
  }
  // Multi-level: chain field accesses
  return `Val.field' ${base} "${fieldPath.join(".")}"`;
}

function sanitizeTag(tag: string): string {
  return tag.replace(/[^a-zA-Z0-9_]/g, "_").replace(/-/g, "_");
}
