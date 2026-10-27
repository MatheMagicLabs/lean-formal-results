/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     Pi.nnnorm_extend_le'
Source:      Mathlib @ a02a63c2, Mathlib/Analysis/Normed/Group/Constructions.lean, line 410
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  O2-repair-vs-resample, arm B, verified in round 0 (round 0 = first attempt)
Prover:      claude-opus-5-5
Setup:       Opus 5.5: arm B = one attempt plus up to 3 repair rounds with Lean error messages; arm A = 4 independent attempts (attempt k)
Check:       the proof replaced the human proof in the Mathlib file above; Lean reported
             0 errors and no `sorry`; sorry/admit/native_decide/search tactics were rejected.
-/

-- (context: the Mathlib file above this declaration)
@[to_additive Pi.nnnorm_extend_le]
theorem Pi.nnnorm_extend_le' (f : ι → ι') (g : ι → E) (j : ι' → E) :
    ‖Function.extend f g j‖₊ ≤ max ‖g‖₊ ‖j‖₊ := by
  classical
  rw [pi_nnnorm_le_iff']
  intro i
  rw [Function.extend_def]
  split_ifs with h
  · exact (nnnorm_le_pi_nnnorm' g _).trans (le_max_left _ _)
  · exact (nnnorm_le_pi_nnnorm' j i).trans (le_max_right _ _)
