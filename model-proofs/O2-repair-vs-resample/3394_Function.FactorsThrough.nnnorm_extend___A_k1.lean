/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     Function.FactorsThrough.nnnorm_extend'
Source:      Mathlib @ a02a63c2, Mathlib/Analysis/Normed/Group/Constructions.lean, line 421
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  O2-repair-vs-resample, arm A, attempt 1, verified in round 0 (round 0 = first attempt)
Prover:      claude-opus-5-5
Setup:       Opus 5.5: arm B = one attempt plus up to 3 repair rounds with Lean error messages; arm A = 4 independent attempts (attempt k)
Check:       the proof replaced the human proof in the Mathlib file above; Lean reported
             0 errors and no `sorry`; sorry/admit/native_decide/search tactics were rejected.
-/

-- (context: the Mathlib file above this declaration)
@[to_additive Function.FactorsThrough.nnnorm_extend]
theorem Function.FactorsThrough.nnnorm_extend' {f : ι → ι'} {g : ι → E} {j : ι' → E}
    (h : FactorsThrough g f) (hj : ‖j‖₊ ≤ ‖g‖₊) :
    ‖extend f g j‖₊ = ‖g‖₊ := by
  apply le_antisymm
  · exact (Pi.nnnorm_extend_le' f g j).trans (max_le le_rfl hj)
  · calc ‖g‖₊ = ‖extend f g j ∘ f‖₊ := by rw [h.extend_comp j]
      _ ≤ _ := pi_nnnorm_comp_le' _ _
