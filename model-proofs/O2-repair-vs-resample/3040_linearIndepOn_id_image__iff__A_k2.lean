/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     linearIndepOn_id_imageₛ_iff
Source:      Mathlib @ a02a63c2, Mathlib/LinearAlgebra/LinearIndependent/Basic.lean, line 275
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  O2-repair-vs-resample, arm A, attempt 2, verified in round 0 (round 0 = first attempt)
Prover:      claude-opus-5-5
Setup:       Opus 5.5: arm B = one attempt plus up to 3 repair rounds with Lean error messages; arm A = 4 independent attempts (attempt k)
Check:       the proof replaced the human proof in the Mathlib file above; Lean reported
             0 errors and no `sorry`; sorry/admit/native_decide/search tactics were rejected.
-/

-- (context: the Mathlib file above this declaration)
theorem linearIndepOn_id_imageₛ_iff {s : Set M} {f : M →ₗ[R] M'} (hf_inj : Set.InjOn f (span R s)) :
    LinearIndepOn R id (f '' s) ↔ LinearIndepOn R id s := by
  refine (linearIndepOn_iff_image (hf_inj.mono subset_span)).symm.trans ?_
  have h : Set.InjOn f (span R (id '' s)) := by rwa [image_id]
  have := f.linearIndepOn_iff_of_injOn h
  exact this
