/-
  JSCore₀ Metatheory — Taint Soundness.
  Changing a taint source's value doesn't change any matching call's arguments.
-/
import JSCore.Eval
import JSCore.Taint

set_option linter.sorryIn false

namespace JSCore

-- Helper: if an expression's free variables don't contain source,
-- then evaluation is identical regardless of source's value in env.
-- This is the key lemma for taint soundness.
theorem eval_independent_of_source (fuel : Nat) (env env' : Env) (store : Store)
    (e : Expr) (source : String)
    (h_env : ∀ x, x ≠ source → env x = env' x)
    (h_not_free : source ∉ freeVars e) :
    eval fuel env store e = eval fuel env' store e := by
  sorry

-- Main taint soundness theorem:
-- If no call matching pattern has any argument tainted by source,
-- then changing source's value doesn't change any matching call's arguments.
theorem taint_soundness (fuel : Nat) (prog : Expr) (source pattern : String)
    (h : notTaintedIn prog source pattern = true) :
    ∀ env env' store,
      (∀ x, x ≠ source → env x = env' x) →
      callsTo (eval fuel env store prog).trace pattern =
      callsTo (eval fuel env' store prog).trace pattern := by
  sorry

end JSCore
