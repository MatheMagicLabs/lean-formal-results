/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     stdIsLinearOrder_iff
Source:      Mathlib @ a02a63c2, Mathlib/Order/Defs/Unbundled.lean, line 192
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  O2-repair-vs-resample, arm B, verified in round 0 (round 0 = first attempt)
Prover:      claude-opus-5-5
Setup:       Opus 5.5: arm B = one attempt plus up to 3 repair rounds with Lean error messages; arm A = 4 independent attempts (attempt k)
Check:       the proof replaced the human proof in the Mathlib file above; Lean reported
             0 errors and no `sorry`; sorry/admit/native_decide/search tactics were rejected.
-/

-- (context: the Mathlib file above this declaration)
theorem stdIsLinearOrder_iff {α : Type*} [LE α] :
    Std.IsLinearOrder α ↔ IsLinearOrder α (· ≤ ·) := by
  constructor
  · intro h
    have hp : IsPartialOrder α (· ≤ ·) := stdIsPartialOrder_iff.mp inferInstance
    have ht : Std.Total (α := α) (· ≤ ·) := by
      first
        | exact inferInstance
        | exact ⟨fun a b => Std.IsLinearPreorder.le_total a b⟩
        | exact ⟨fun a b => Std.le_total a b⟩
    exact { hp, ht with }
  · intro h
    have hp : Std.IsPartialOrder α := stdIsPartialOrder_iff.mpr inferInstance
    have ht : Std.Total (α := α) (· ≤ ·) := ⟨fun a b => total_of (· ≤ ·) a b⟩
    first
      | exact { hp, ht with }
      | exact { hp with }
      | exact { hp with le_total := fun a b => total_of (· ≤ ·) a b }
      | exact { hp with total := fun a b => total_of (· ≤ ·) a b }
