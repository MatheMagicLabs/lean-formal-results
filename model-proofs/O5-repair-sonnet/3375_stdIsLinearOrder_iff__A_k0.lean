/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     stdIsLinearOrder_iff
Source:      Mathlib @ a02a63c2, Mathlib/Order/Defs/Unbundled.lean, line 192
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  O5-repair-sonnet, arm A, attempt 0, verified in round 0 (round 0 = first attempt)
Prover:      claude-sonnet-5-5
Setup:       Sonnet 5.5: arm B = repair loop; arm A = independent attempts
Check:       the proof replaced the human proof in the Mathlib file above; Lean reported
             0 errors and no `sorry`; sorry/admit/native_decide/search tactics were rejected.
-/

-- (context: the Mathlib file above this declaration)
theorem stdIsLinearOrder_iff {α : Type*} [LE α] :
    Std.IsLinearOrder α ↔ IsLinearOrder α (· ≤ ·) := by
  refine ⟨fun _ ↦ {}, fun _ ↦ { toIsPartialOrder := ?_, le_total _ _ := total_of (· ≤ ·) _ _ }⟩
  exact stdIsPartialOrder_iff.mpr inferInstance
