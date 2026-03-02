/-
  JSCore₀ Metatheory — Composition.
  Trace concatenation preserves per-call properties.
-/
import JSCore.Eval
import JSCore.Metatheory.TraceComposition

namespace JSCore

-- If P holds for all entries in t1 and t2, then for all entries in t1 ++ t2
theorem trace_append_preserves (t1 t2 : List TraceEntry) (P : TraceEntry → Prop)
    (h1 : ∀ e ∈ t1, P e) (h2 : ∀ e ∈ t2, P e) :
    ∀ e ∈ t1 ++ t2, P e := by
  intro e he
  rw [List.mem_append] at he
  cases he with
  | inl h => exact h1 e h
  | inr h => exact h2 e h

-- Same but for CallRecords (via extractCalls)
theorem calls_append_preserves (t1 t2 : List TraceEntry) (P : CallRecord → Prop)
    (h1 : ∀ c ∈ extractCalls t1, P c) (h2 : ∀ c ∈ extractCalls t2, P c) :
    ∀ c ∈ extractCalls (t1 ++ t2), P c := by
  rw [extractCalls_append]
  intro c hc
  rw [List.mem_append] at hc
  cases hc with
  | inl h => exact h1 c h
  | inr h => exact h2 c h

-- A single-entry trace containing a call satisfying P preserves P
theorem call_entry_preserves (cr : CallRecord) (P : CallRecord → Prop) (h : P cr) :
    ∀ c ∈ extractCalls [TraceEntry.call cr], P c := by
  intro c hc
  simp [extractCalls, List.filterMap] at hc
  rw [hc]
  exact h

end JSCore
