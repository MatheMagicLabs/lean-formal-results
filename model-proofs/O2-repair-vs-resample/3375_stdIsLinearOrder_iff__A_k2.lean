/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     stdIsLinearOrder_iff
Source:      Mathlib @ a02a63c2, Mathlib/Order/Defs/Unbundled.lean, line 192
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  O2-repair-vs-resample, arm A, attempt 2, verified in round 0 (round 0 = first attempt)
Prover:      claude-opus-5-5
Setup:       Opus 5.5: arm B = one attempt plus up to 3 repair rounds with Lean error messages; arm A = 4 independent attempts (attempt k)
Check:       the proof replaced the human proof in the Mathlib file above; Lean reported
             0 errors and no `sorry`; sorry/admit/native_decide/search tactics were rejected.
-/

-- (context: the Mathlib file above this declaration)
theorem stdIsLinearOrder_iff {α : Type*} [LE α] :
    Std.IsLinearOrder α ↔ IsLinearOrder α (· ≤ ·) := by
  refine ⟨fun h ↦ { toIsPartialOrder := stdIsPartialOrder_iff.mp inferInstance,
                     total := h.le_total },
          fun _ ↦ { toIsPartialOrder := stdIsPartialOrder_iff.mpr inferInstance,
                     le_total := fun a b => Std.Total.total a b }⟩
