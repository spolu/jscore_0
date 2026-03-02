/-
  JSCore₀ Metatheory — Loop Invariant.
  The main forOf_invariant theorem.
-/
import JSCore.Eval

namespace JSCore

-- The main loop invariant theorem.
theorem forOf_invariant (fuel : Nat) (env : Env) (store : Store)
    (x : String) (elems : List Val) (body : Expr)
    (P : TraceEntry → Prop) (I : Store → Prop)
    (pfx : List TraceEntry)
    (h_pfx : ∀ e ∈ pfx, P e)
    (h_init : I store)
    (h_step : ∀ elem store_i, I store_i →
      let r := eval fuel (env.set x elem) store_i body
      I r.store ∧ ∀ e ∈ r.trace, P e) :
    let result := evalForOf fuel env store x elems body pfx
    (∀ e ∈ result.trace, P e) ∧ I result.store := by
  induction elems generalizing store pfx with
  | nil =>
    simp [evalForOf, mkResult]
    exact ⟨h_pfx, h_init⟩
  | cons hd tl ih =>
    simp only [evalForOf]
    have h_hd := h_step hd store h_init
    obtain ⟨h_I_r, h_P_r⟩ := h_hd
    have h_pfx_r : ∀ e ∈ pfx ++ (eval fuel (env.set x hd) store body).trace, P e := by
      intro e he
      rw [List.mem_append] at he
      cases he with
      | inl h => exact h_pfx e h
      | inr h => exact h_P_r e h
    -- Case split on the outcome
    split
    next => -- .ok
      exact ih _ _ h_pfx_r h_I_r
    all_goals {
      simp only [mkResult]
      exact ⟨h_pfx_r, h_I_r⟩
    }

-- Convenience version with empty prefix
theorem forOf_invariant' (fuel : Nat) (env : Env) (store : Store)
    (x : String) (elems : List Val) (body : Expr)
    (P : TraceEntry → Prop) (I : Store → Prop)
    (h_init : I store)
    (h_step : ∀ elem store_i, I store_i →
      let r := eval fuel (env.set x elem) store_i body
      I r.store ∧ ∀ e ∈ r.trace, P e) :
    let result := evalForOf fuel env store x elems body []
    (∀ e ∈ result.trace, P e) ∧ I result.store :=
  forOf_invariant fuel env store x elems body P I [] (fun _ h => absurd h (List.not_mem_nil _))
    h_init h_step

end JSCore
