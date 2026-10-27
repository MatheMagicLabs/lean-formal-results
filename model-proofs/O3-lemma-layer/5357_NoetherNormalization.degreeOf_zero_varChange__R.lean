/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     NoetherNormalization.degreeOf_zero_varChange
Source:      Mathlib @ a02a63c2, Mathlib/RingTheory/NoetherNormalization.lean, line 100
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  O3-lemma-layer, arm R, verified in round 2 (round 0 = first attempt)
Prover:      claude-opus-5-5
Setup:       Opus 5.5 with repair loop: arm R = repair only; arm RS = repair plus the Lean-checked lemma layer
Check:       the proof replaced the human proof in the Mathlib file above; Lean reported
             0 errors and no `sorry`; sorry/admit/native_decide/search tactics were rejected.
-/

open Polynomial MvPolynomial Ideal Nat RingHom List
variable {k : Type*} [Field k] {n : ℕ} (f : MvPolynomial (Fin (n + 1)) k)
variable (v w : Fin (n + 1) →₀ ℕ)
namespace NoetherNormalization
section equivT
local notation3 "up" => 2 + f.totalDegree
variable {f v} in
local notation3 "r" => fun (i : Fin (n + 1)) ↦ up ^ i.1

private lemma degreeOf_zero_varChange {a : k} (ha : a ≠ 0) :
    ((varChange f) (monomial v a)).degreeOf 0 = ∑ i : Fin (n + 1), (r i) * v i := by
  rw [← natDegree_finSuccEquiv, monomial_eq, Finsupp.prod_pow v fun a ↦ X a]
  simp only [varChange, T1, Fin.prod_univ_succ, Fin.sum_univ_succ, map_mul, map_prod, map_pow,
    AlgEquiv.ofAlgHom_apply, MvPolynomial.aeval_C, MvPolynomial.aeval_X, if_pos,
    Fin.succ_ne_zero, ite_false, one_smul, map_add, finSuccEquiv_X_zero,
    finSuccEquiv_X_succ, MvPolynomial.algebraMap_eq]
  have h (i : Fin n) :
      (Polynomial.C (X (R := k) i) + Polynomial.X ^ (2 + f.totalDegree) ^ (i.succ).1) ^ v i.succ
        ≠ 0 :=
    pow_ne_zero (v i.succ) (leadingCoeff_ne_zero.mp <| by
      simp [add_comm, leadingCoeff_X_pow_add_C])
  have hp : (Polynomial.X : Polynomial (MvPolynomial (Fin n) k)) ^ v 0 *
      ∏ i : Fin n, (Polynomial.C (X (R := k) i) +
        Polynomial.X ^ (2 + f.totalDegree) ^ (i.succ).1) ^ v i.succ ≠ 0 :=
    mul_ne_zero (pow_ne_zero _ Polynomial.X_ne_zero)
      (Finset.prod_ne_zero_iff.mpr (fun i _ ↦ h i))
  rw [natDegree_mul (by simp [ha]) hp, natDegree_finSuccEquiv, degreeOf_C,
    natDegree_mul (pow_ne_zero _ Polynomial.X_ne_zero)
      (Finset.prod_ne_zero_iff.mpr (fun i _ ↦ h i)),
    natDegree_X_pow, natDegree_prod _ _ (fun i _ ↦ h i)]
  simp only [zero_add, Fin.val_zero, pow_zero, one_mul]
  congr 1
  refine Finset.sum_congr rfl (fun i _ ↦ ?_)
  rw [natDegree_pow, add_comm (Polynomial.C _), natDegree_X_pow_add_C, mul_comm]
