/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     NoetherNormalization.leadingCoeff_finSuccEquiv_varChange
Source:      Mathlib @ a02a63c2, Mathlib/RingTheory/NoetherNormalization.lean, line 127
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  O2-repair-vs-resample, arm A, attempt 3, verified in round 0 (round 0 = first attempt)
Prover:      claude-opus-5-5
Setup:       Opus 5.5: arm B = one attempt plus up to 3 repair rounds with Lean error messages; arm A = 4 independent attempts (attempt k)
Check:       the proof replaced the human proof in the Mathlib file above; Lean reported
             0 errors and no `sorry`; sorry/admit/native_decide/search tactics were rejected.
-/

-- (context: the Mathlib file above this declaration)
private lemma leadingCoeff_finSuccEquiv_varChange :
    (finSuccEquiv k n <| varChange f <| monomial v <| f.coeff v).leadingCoeff =
    algebraMap k _ (f.coeff v) := by
  have h (i : Fin n) :
      (Polynomial.C (X (R := k) i) +
        Polynomial.X ^ (2 + f.totalDegree) ^ (i.succ).1).leadingCoeff = 1 := by
    rw [add_comm]
    exact leadingCoeff_X_pow_add_C (by positivity)
  rw [monomial_eq, Finsupp.prod_pow v fun a ↦ X a]
  simp only [Fin.prod_univ_succ, map_mul, map_prod, map_pow,
    AlgEquiv.ofAlgHom_apply, MvPolynomial.aeval_C, MvPolynomial.aeval_X, ↓reduceIte,
    Fin.succ_ne_zero, if_false, ite_false, one_smul, map_add, finSuccEquiv_X_zero,
    finSuccEquiv_X_succ, AlgEquiv.commutes]
  simp only [leadingCoeff_mul, leadingCoeff_prod, leadingCoeff_pow, h,
    Polynomial.algebraMap_apply, leadingCoeff_C, leadingCoeff_X, one_pow,
    Finset.prod_const_one, mul_one]
