/-
  JSCore₀ Metatheory — ForOf CallsTo Infrastructure.

  Bridges the gap between eval's inline foldl for forOf and reusable proof lemmas.
  Provides:
  - `forOfFoldStep`: named version of eval's inline forOf lambda
  - `forOfFold_callsTo`: main invariant for callsTo properties over forOf foldl
  - `eval_forOf_non_arr_trace`: non-array case produces no additional trace
-/
import JSCore.Eval
import JSCore.Metatheory.EvalEq
import JSCore.Metatheory.TraceComposition

namespace JSCore

/-- Generic foldl step for forOf — named version of the inline lambda in eval's forOf case. -/
def forOfFoldStep (fuel : Nat) (env : Env) (x : String) (body : Expr)
    (acc : Result) (elem : Val) : Result :=
  match acc.outcome with
  | .ok _ =>
    let r := eval fuel (env.set x elem) acc.store body
    match r.outcome with
    | .brk => mkResult (.ok .none) r.store (acc.trace ++ r.trace)
    | .returned v => mkResult (.returned v) r.store (acc.trace ++ r.trace)
    | _ => mkResult r.outcome r.store (acc.trace ++ r.trace)
  | _ => acc

/-- The inline lambda in eval's forOf case equals forOfFoldStep. -/
theorem eval_forOf_foldl_step (fuel : Nat) (env : Env) (x : String)
    (body : Expr) (elems : List Val) (acc : Result) :
    elems.foldl (fun (acc : Result) (elem : Val) =>
      match acc.outcome with
      | .ok _ =>
        let r := eval fuel (env.set x elem) acc.store body
        match r.outcome with
        | .brk => mkResult (.ok .none) r.store (acc.trace ++ r.trace)
        | .returned v => mkResult (.returned v) r.store (acc.trace ++ r.trace)
        | _ => mkResult r.outcome r.store (acc.trace ++ r.trace)
      | _ => acc
    ) acc = elems.foldl (forOfFoldStep fuel env x body) acc := rfl

/-- forOfFoldStep when acc outcome is ok reduces to the body evaluation. -/
theorem forOfFoldStep_ok {fuel : Nat} {env : Env} {x : String} {body : Expr}
    {acc : Result} {elem : Val} {v : Val}
    (h : acc.outcome = .ok v) :
    forOfFoldStep fuel env x body acc elem =
    (let r := eval fuel (env.set x elem) acc.store body
     match r.outcome with
     | .brk => mkResult (.ok .none) r.store (acc.trace ++ r.trace)
     | .returned rv => mkResult (.returned rv) r.store (acc.trace ++ r.trace)
     | _ => mkResult r.outcome r.store (acc.trace ++ r.trace)) := by
  simp [forOfFoldStep, h]

/-- forOfFoldStep is identity when acc outcome is not ok. -/
theorem forOfFoldStep_not_ok {fuel : Nat} {env : Env} {x : String} {body : Expr}
    {acc : Result} {elem : Val}
    (h : ∀ v, acc.outcome ≠ .ok v) :
    forOfFoldStep fuel env x body acc elem = acc := by
  unfold forOfFoldStep
  cases h_out : acc.outcome with
  | ok v => exact absurd h_out (h v)
  | error _ => rfl
  | brk => rfl
  | returned _ => rfl

/-- foldl with forOfFoldStep is identity when acc outcome is not ok. -/
theorem foldl_forOfFoldStep_not_ok {fuel : Nat} {env : Env} {x : String}
    {body : Expr} (elems : List Val) (acc : Result)
    (h : ∀ v, acc.outcome ≠ .ok v) :
    elems.foldl (forOfFoldStep fuel env x body) acc = acc := by
  induction elems generalizing acc with
  | nil => rfl
  | cons hd tl ih =>
    simp only [List.foldl]
    rw [forOfFoldStep_not_ok h]
    exact ih acc h

/-- Main invariant: callsTo property P (guarded by store invariant I) is preserved
    across forOf foldl iterations. This is the foldl-based analog of forOf_invariant.

    Key insight: eval's forOf uses inline List.foldl (to avoid mutual recursion),
    while evalForOf uses explicit recursion. They differ on break semantics
    (foldl continues after break, evalForOf stops). This lemma works directly
    on the foldl form that eval actually produces. -/
theorem forOfFold_callsTo (fuel : Nat) (env : Env)
    (x : String) (elems : List Val) (body : Expr) (pattern : String)
    (P : CallRecord → Prop) (I : Store → Prop)
    (acc : Result)
    (h_acc_I : I acc.store)
    (h_acc_calls : ∀ c ∈ callsTo acc.trace pattern, P c)
    (h_step : ∀ elem store_i, I store_i →
      let r := eval fuel (env.set x elem) store_i body
      I r.store ∧ ∀ c ∈ callsTo r.trace pattern, P c) :
    let result := elems.foldl (forOfFoldStep fuel env x body) acc
    (∀ c ∈ callsTo result.trace pattern, P c) ∧ I result.store := by
  induction elems generalizing acc with
  | nil => exact ⟨h_acc_calls, h_acc_I⟩
  | cons hd tl ih =>
    simp only [List.foldl]
    -- Case split on whether acc is ok (determines if step runs)
    cases h_out : acc.outcome with
    | ok v =>
      -- Step runs: rewrite forOfFoldStep using h_out
      rw [forOfFoldStep_ok h_out]
      -- Get properties of this iteration
      have ⟨h_I', h_calls'⟩ := h_step hd acc.store h_acc_I
      have h_combined := forall_calls_append _ _ _ _ h_acc_calls h_calls'
      -- Case split on body outcome to determine the step result
      cases h_body : (eval fuel (env.set x hd) acc.store body).outcome with
      | ok v' =>
        -- Body succeeded: foldl continues with new accumulator
        simp only [h_body, mkResult]
        exact ih _ h_I' h_combined
      | brk =>
        -- Break: outcome becomes .ok .none, foldl continues
        simp only [h_body, mkResult]
        exact ih _ h_I' h_combined
      | returned rv =>
        -- Returned: foldl stops (outcome is not ok)
        simp only [h_body, mkResult]
        rw [foldl_forOfFoldStep_not_ok tl _ (by intro w hw; simp [mkResult] at hw)]
        exact ⟨by simpa [mkResult] using h_combined, h_I'⟩
      | error e =>
        -- Error: foldl stops (outcome is not ok)
        simp only [h_body, mkResult]
        rw [foldl_forOfFoldStep_not_ok tl _ (by intro w hw; simp [mkResult] at hw)]
        exact ⟨by simpa [mkResult] using h_combined, h_I'⟩
    | error _ =>
      -- acc is not ok: step is identity, foldl on tl is also identity
      rw [forOfFoldStep_not_ok (by rw [h_out]; intro v; exact Outcome.noConfusion)]
      rw [foldl_forOfFoldStep_not_ok tl _ (by rw [h_out]; intro v; exact Outcome.noConfusion)]
      exact ⟨h_acc_calls, h_acc_I⟩
    | brk =>
      rw [forOfFoldStep_not_ok (by rw [h_out]; intro v; exact Outcome.noConfusion)]
      rw [foldl_forOfFoldStep_not_ok tl _ (by rw [h_out]; intro v; exact Outcome.noConfusion)]
      exact ⟨h_acc_calls, h_acc_I⟩
    | returned _ =>
      rw [forOfFoldStep_not_ok (by rw [h_out]; intro v; exact Outcome.noConfusion)]
      rw [foldl_forOfFoldStep_not_ok tl _ (by rw [h_out]; intro v; exact Outcome.noConfusion)]
      exact ⟨h_acc_calls, h_acc_I⟩

/-- Non-array case: forOf trace equals array expr trace (no loop iterations run). -/
theorem eval_forOf_non_arr_trace {n : Nat} {env : Env} {store : Store}
    {x : String} {arrExpr body : Expr}
    (h : ∀ elems, (eval n env store arrExpr).outcome ≠ .ok (.arr elems)) :
    (eval (n + 1) env store (.forOf x arrExpr body)).trace =
    (eval n env store arrExpr).trace := by
  simp only [eval]
  generalize eval n env store arrExpr = ra at h ⊢
  cases h_out : ra.outcome with
  | ok v =>
    cases v with
    | arr elems => exact absurd h_out (h elems)
    | str _ => simp [mkResult]
    | num _ => simp [mkResult]
    | bool _ => simp [mkResult]
    | none => simp [mkResult]
    | obj _ => simp [mkResult]
  | error _ => rfl
  | brk => rfl
  | returned _ => rfl

end JSCore
