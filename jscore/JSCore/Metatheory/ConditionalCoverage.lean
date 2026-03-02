/-
  JSCore₀ Metatheory — Conditional Coverage.
  If a property holds on both branches, it holds on the conditional.
-/
import JSCore.Eval

namespace JSCore

theorem ite_covers (fuel : Nat) (env : Env) (store : Store) (cond thn els : Expr)
    (P : List TraceEntry → Prop)
    (h_cond : ∃ b, (eval fuel env store cond).outcome = .ok (.bool b))
    (h_true : (eval fuel env store cond).outcome = .ok (.bool true) →
      P ((eval fuel env store cond).trace ++ (eval fuel env (eval fuel env store cond).store thn).trace))
    (h_false : (eval fuel env store cond).outcome = .ok (.bool false) →
      P ((eval fuel env store cond).trace ++ (eval fuel env (eval fuel env store cond).store els).trace)) :
    P (eval (fuel + 1) env store (.ite cond thn els)).trace := by
  simp [eval]
  obtain ⟨b, hb⟩ := h_cond
  cases b with
  | true =>
    simp [hb, mkResult]
    exact h_true hb
  | false =>
    simp [hb, mkResult]
    exact h_false hb

end JSCore
