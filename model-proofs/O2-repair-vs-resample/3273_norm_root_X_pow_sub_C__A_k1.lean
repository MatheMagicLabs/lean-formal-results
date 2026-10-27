/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     norm_root_X_pow_sub_C
Source:      Mathlib @ a02a63c2, Mathlib/FieldTheory/KummerExtension.lean, line 108
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  O2-repair-vs-resample, arm A, attempt 1, verified in round 0 (round 0 = first attempt)
Prover:      claude-opus-5-5
Setup:       Opus 5.5: arm B = one attempt plus up to 3 repair rounds with Lean error messages; arm A = 4 independent attempts (attempt k)
Check:       the proof replaced the human proof in the Mathlib file above; Lean reported
             0 errors and no `sorry`; sorry/admit/native_decide/search tactics were rejected.
-/

-- (context: the Mathlib file above this declaration)
theorem norm_root_X_pow_sub_C {n : ℕ} {a : K} (hn : n ≠ 0) :
    Algebra.norm K (root (X ^ n - C a)) = (-1) ^ n * -a := by
  have hf := monic_X_pow_sub_C a hn
  rw [← AdjoinRoot.powerBasis_gen hf.ne_zero,
    Algebra.PowerBasis.norm_gen_eq_coeff_zero_minpoly,
    AdjoinRoot.minpoly_powerBasis_gen_of_monic hf, AdjoinRoot.powerBasis_dim,
    natDegree_X_pow_sub_C]
  simp [Ne.symm hn]
