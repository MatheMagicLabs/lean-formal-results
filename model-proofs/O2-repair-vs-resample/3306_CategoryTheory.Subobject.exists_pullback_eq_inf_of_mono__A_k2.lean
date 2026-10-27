/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     CategoryTheory.Subobject.exists_pullback_eq_inf_of_mono
Source:      Mathlib @ a02a63c2, Mathlib/CategoryTheory/Subobject/Lattice.lean, line 447
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  O2-repair-vs-resample, arm A, attempt 2, verified in round 0 (round 0 = first attempt)
Prover:      claude-opus-5-5
Setup:       Opus 5.5: arm B = one attempt plus up to 3 repair rounds with Lean error messages; arm A = 4 independent attempts (attempt k)
Check:       the proof replaced the human proof in the Mathlib file above; Lean reported
             0 errors and no `sorry`; sorry/admit/native_decide/search tactics were rejected.
-/

-- (context: the Mathlib file above this declaration)
theorem exists_pullback_eq_inf_of_mono [HasImages C] (f : X ⟶ Y) [Mono f] (Y' : Subobject Y) :
    («exists» f).obj ((pullback f).obj Y') = Y' ⊓ mk f := by
  rw [inf_comm, exists_iso_map]
  exact (inf_eq_map_pullback' (MonoOver.mk f) Y').symm
