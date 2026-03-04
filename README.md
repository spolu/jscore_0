# JSCore₀

Annotated TypeScript to Lean 4 proofs. Agents write code and proofs, humans review one-line annotations, the Lean kernel checks everything.

```
annotated .ts  -->  extractor (ts-morph)  -->  Lean 4 AST + theorems  -->  lake build  -->  verified
```

## Why

Agents produce code faster than humans can review it. JSCore₀ replaces code review with three lightweight comment annotations that capture what the code should do. The agent generates both the implementation and the proof. If the proof checks, the code matches the spec. If it doesn't, `lake build` fails. No human reads the implementation.

## The three annotations

```typescript
// @requires auth.workspaceId > 0
// @invariant ws-isolation: ∀ call db.* (c) => c.where.workspaceId = auth.workspaceId
async function lookupProject(auth: Auth, projectId: string) {
  const project = await db.project.findUnique({
    where: { id: projectId, workspaceId: auth.workspaceId },
  });
  // @ensures project.workspaceId = auth.workspaceId
  return project;
}
```

- **`@requires`** - caller must satisfy this. Becomes a hypothesis in the proof.
- **`@invariant`** - proved over every execution. Lean kernel checks it.
- **`@ensures`** - post-condition on an external call result. Bridges what types can't express.

## Full example

**Input:** `rotateApiKey.ts`

```typescript
// @invariant no-secret-leak: ¬ tainted apiKey in call logger.*
async function rotateApiKey(apiKey: string, keyId: string) {
  const newKey = await generateKey();
  await db.apiKey.update({ where: { id: keyId }, data: { key: apiKey } });
  await logger.info("rotated:" + keyId);
}
```

**Output:** `rotateApiKey_jscore.lean` (generated, proved by `native_decide`)

```lean
def rotateApiKey_body : Expr :=
  (.call "generateKey" [] "newKey"
    (.call "db.apiKey.update"
      [("where", (.obj [("id", (.var "keyId"))])),
       ("data", (.obj [("key", (.var "apiKey"))]))]
      "__void_0"
      (.call "logger.info"
        [("arg0", (.binOp .add (.strLit "rotated:") (.var "keyId")))]
        "__void_1" Expr.none)))

theorem rotateApiKey_no_secret_leak
    : notTaintedIn rotateApiKey_body "apiKey" "logger.*" = true := by
  native_decide
```

The taint analysis walks the AST, tracks that `apiKey` flows to `db.apiKey.update` but never reaches any `logger.*` call. `native_decide` reduces the entire check to `true` at compile time.

## What you can prove

```
∀ call db.* (c) => c.where.workspaceId = auth.workspaceId     -- workspace isolation
¬ tainted secret in call logger.*                               -- no secret leak
∀ call db.account.update (u) => sum(u.data.balance) = 0        -- conservation
∃ call permissions.check (p) before u where p.action = "write" -- auth gate
¬ ∃ call db.*.update                                            -- read-only
∀ call db.*.findMany (f) => f.take = pageSize                  -- page bounded
```

Three proof shapes:
- **Taint analysis** (syntactic, `native_decide`): does sensitive data reach a call target?
- **Nonexistence** (syntactic, `native_decide`): does a call pattern appear in the AST?
- **Runtime properties** (inductive proofs over eval): properties about every call's arguments across all execution paths

## Taint precision

```typescript
// secret flows to crypto.hmac (whitelisted), signature is safe, logLine is safe
// @invariant no-secret-in-logs: ¬ tainted secret in call logger.*
async function signAndLog(secret: string, userId: string, action: string) {
  const payload = userId + ":" + action;
  const signature = await crypto.hmac(secret, payload);  // whitelisted
  const logLine = payload + "|sig:" + signature;
  await logger.info(logLine);  // safe: signature not tainted
}

// secret flows to unsafeHash.digest (NOT whitelisted), tag is tainted, leaks
// @invariant secret-leaks-to-logs: tainted secret in call logger.*
async function leakyLog(secret: string, userId: string) {
  const tag = await unsafeHash.digest(secret);  // result stays tainted
  const logLine = userId + ":" + tag;
  await logger.info(logLine);  // leak: tag carries taint
}
```

Both proved by `native_decide`. The analysis tracks taint through binding chains and call results. Whitelisting a callee (`@invariant no-taint: ¬ tainted key in result` on the declaration) marks its output as clean.

## Building

```bash
# Lean formalism
export PATH="$HOME/.elan/bin:$PATH"
cd jscore && lake build JSCore

# Extractor
cd extractor && npx tsc
node dist/index.js extract --out-dir ../examples ../examples/*.ts

# Verify all proofs
cd examples && lake build
```

Requires: Lean 4 v4.16.0 (via elan), Node.js, TypeScript.

## Architecture

```
jscore/JSCore/          Lean 4 formalism (~2,870 LOC)
  Syntax.lean           26-constructor Expr type (CPS-style calls)
  Values.lean           Val (str/num/bool/none/obj/arr), Env, Store
  Eval.lean             fuel-bounded evaluator, structural recursion
  Trace.lean            CallRecord, callsTo, pattern matching with wildcards
  Taint.lean            syntactic taint analysis, notTaintedIn (decidable)
  Metatheory/           equation lemmas, trace composition, loop invariants, taint soundness
  Tactics.lean          trace_simp, by_taint, by_ordering

extractor/src/          TypeScript extractor (~1,000 LOC)
  ast-to-jscore.ts      ts-morph AST to JsCoreExpr (CPS translation)
  lean-emitter.ts       JsCoreExpr to Lean source text
  lean-theorem.ts       annotations to theorem statements
  proof-merge.ts        proof-preserving regeneration

examples/               annotated TS + generated Lean proofs
  *.ts                  source with @requires/@invariant/@ensures
  *_jscore.lean         extracted defs + proved theorems
```

Re-running the extractor preserves existing proofs. New `def` bodies and theorem statements are regenerated, but non-sorry proof bodies and private helper lemmas are spliced back in.

## How proofs work

The eval function maps `Expr` to `Result` (outcome + store + trace). Proofs step through eval one constructor at a time using equation lemmas (`eval_call_eq`, `eval_letConst_eq`, etc.), then inspect the trace.

For loops, `forOfFold_callsTo` provides a reusable invariant: given a per-iteration property on call records and a store invariant, it proves the property holds across the entire foldl.

For taint, `notTaintedIn` is a Bool function that walks the AST. `taint_soundness` proves: if `notTaintedIn` returns true, changing the tainted source's value does not change any matching call's arguments.

## Design doc

See [PROPOSAL.md](PROPOSAL.md) for the full system design, motivation, formal semantics, metatheory, and 20 real invariant examples.
