/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     NoetherNormalization.leadingCoeff_finSuccEquiv_varChange
Source:      Mathlib @ a02a63c2, Mathlib/RingTheory/NoetherNormalization.lean, line 127
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  O2-repair-vs-resample, arm B, verified in round 2 (round 0 = first attempt)
Prover:      claude-opus-5-5
Setup:       Opus 5.5: arm B = one attempt plus up to 3 repair rounds with Lean error messages; arm A = 4 independent attempts (attempt k)
Check:       the proof replaced the human proof in the Mathlib file above; Lean reported
             0 errors and no `sorry`; sorry/admit/native_decide/search tactics were rejected.
-/

-- (context: the Mathlib file above this declaration)
private lemma leadingCoeff_finSuccEquiv_varChange :
    (finSuccEquiv k n <| varChange f <| monomial v <| f.coeff v).leadingCoeff =
    algebraMap k _ (f.coeff v) := by
  have h (p : MvPolynomial (Fin n) k) (j : ℕ) :
      (Polynomial.C p + Polynomial.X ^ ((2 + f.totalDegree) ^ j)).leadingCoeff = 1 := by
    rw [add_comm, leadingCoeff_X_pow_add_C (Nat.one_le_pow _ _ (by lia))]
  rw [monomial_eq, Finsupp.prod_pow v fun a ↦ X a]
  simp [Fin.prod_univ_succ, leadingCoeff_mul, leadingCoeff_prod, h, finSuccEquiv_X_zero,
    finSuccEquiv_X_succ]
  rw [← MvPolynomial.algebraMap_eq, AlgEquiv.commutes, Polynomial.algebraMap_apply,
    leadingCoeff_C]
  rw [MvPolynomial.algebraMap_eq]
