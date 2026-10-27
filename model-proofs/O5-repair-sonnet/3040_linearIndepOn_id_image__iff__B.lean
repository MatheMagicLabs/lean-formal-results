/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     linearIndepOn_id_imageₛ_iff
Source:      Mathlib @ a02a63c2, Mathlib/LinearAlgebra/LinearIndependent/Basic.lean, line 275
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  O5-repair-sonnet, arm B, verified in round 0 (round 0 = first attempt)
Prover:      claude-sonnet-5-5
Setup:       Sonnet 5.5: arm B = repair loop; arm A = independent attempts
Check:       the proof replaced the human proof in the Mathlib file above; Lean reported
             0 errors and no `sorry`; sorry/admit/native_decide/search tactics were rejected.
-/

-- (context: the Mathlib file above this declaration)
theorem linearIndepOn_id_imageₛ_iff {s : Set M} {f : M →ₗ[R] M'} (hf_inj : Set.InjOn f (span R s)) :
    LinearIndepOn R id (f '' s) ↔ LinearIndepOn R id s := by
  have hinj : Set.InjOn f s := hf_inj.mono subset_span
  have h1 : LinearIndepOn R (f ∘ (id : M → M)) s ↔ LinearIndepOn R (id : M → M) s :=
    f.linearIndepOn_iff_of_injOn (by simpa using hf_inj)
  rw [← linearIndepOn_iff_image (f := f) hinj]
  exact h1
