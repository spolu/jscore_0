/-
  JSCore₀ Metatheory — Env Stability.
  Values in Env are never affected by Store mutations.
-/
import JSCore.Eval

namespace JSCore

-- Syntactic check: expression never assigns to variable x
def notMutatedIn (x : String) : Expr → Prop
  | .letMut y _ body => x ≠ y ∧ notMutatedIn x body
  | .assign y _ body => x ≠ y ∧ notMutatedIn x body
  | .letConst _ e body => notMutatedIn x e ∧ notMutatedIn x body
  | .seq e1 e2 => notMutatedIn x e1 ∧ notMutatedIn x e2
  | .ite c t f => notMutatedIn x c ∧ notMutatedIn x t ∧ notMutatedIn x f
  | .forOf _ arrExpr body => notMutatedIn x arrExpr ∧ notMutatedIn x body
  | .whileLoop _ c body => notMutatedIn x c ∧ notMutatedIn x body
  | .call _ _ _ body => notMutatedIn x body
  | .tryCatch body _ handler => notMutatedIn x body ∧ notMutatedIn x handler
  | .ret e => notMutatedIn x e
  | .throw e => notMutatedIn x e
  | .push y _ => x ≠ y
  | .binOp _ e1 e2 => notMutatedIn x e1 ∧ notMutatedIn x e2
  | .unOp _ e => notMutatedIn x e
  | _ => True

-- Env lookup is stable across different stores when x is not in store
theorem env_stable (env : Env) (store store' : Store) (x : String) (v : Val)
    (_h_env : env x = some v)
    (h_not_in_store : store x = .none)
    (h_not_in_store' : store' x = .none) :
    lookup env store x = lookup env store' x := by
  simp [lookup, h_not_in_store, h_not_in_store']

-- Simple helper: Env.set on a different key preserves the original key
theorem Env.set_ne {env : Env} {x y : String} {v : Val} (h : x ≠ y) :
    (env.set y v) x = env x := by
  simp [Env.set, h]

-- Simple helper: Store.set on a different key preserves the original key
theorem Store.set_ne {store : Store} {x y : String} {v : Val} (h : x ≠ y) :
    (store.set y v) x = store x := by
  simp [Store.set, h]

-- If store x = none and we set a different key, store x remains none
theorem Store.set_preserves_none {store : Store} {x y : String} {v : Val}
    (h_ne : x ≠ y) (h_none : store x = .none) :
    (store.set y v) x = .none := by
  simp [Store.set, h_ne, h_none]

end JSCore
