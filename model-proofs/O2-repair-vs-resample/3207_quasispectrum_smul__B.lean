/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     quasispectrum_smul
Source:      Mathlib @ a02a63c2, Mathlib/Algebra/Algebra/Spectrum/Quasispectrum.lean, line 308
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  O2-repair-vs-resample, arm B, verified in round 0 (round 0 = first attempt)
Prover:      claude-opus-5-5
Setup:       Opus 5.5: arm B = one attempt plus up to 3 repair rounds with Lean error messages; arm A = 4 independent attempts (attempt k)
Check:       the proof replaced the human proof in the Mathlib file above; Lean reported
             0 errors and no `sorry`; sorry/admit/native_decide/search tactics were rejected.
-/

-- (context: the Mathlib file above this declaration)
theorem quasispectrum_smul {R A : Type*} [Semifield R] [NonUnitalRing A] [Module R A]
    (k : R) (a : A) : quasispectrum R (k • a) = k • quasispectrum R a := by
  by_cases hk : k = 0
  · subst hk
    rw [zero_smul R a, Set.zero_smul_set (quasispectrum.nonempty R a), quasispectrum.zero_eq]
    first
      | exact Set.singleton_zero
      | rfl
      | simp
  · first
      | exact quasispectrum_unit_smul (Units.mk0 k hk) a
      | simpa [Units.smul_def] using quasispectrum_unit_smul (Units.mk0 k hk) a
