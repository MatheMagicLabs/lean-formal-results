/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     NoetherNormalization.degreeOf_zero_varChange
Source:      Mathlib @ a02a63c2, Mathlib/RingTheory/NoetherNormalization.lean, line 100
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  O4-layer-with-search, arm RT, verified in round 1 (round 0 = first attempt)
Prover:      claude-opus-5-5
Setup:       Opus 5.5 with repair loop, lemma layer and name search (arm RT)
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
  simp only [varChange, T1, Fin.prod_univ_succ, map_mul, map_prod, map_pow,
    AlgEquiv.ofAlgHom_apply, MvPolynomial.aeval_C, MvPolynomial.aeval_X, ↓reduceIte,
    Fin.succ_ne_zero, if_false, ite_false, one_smul, map_add, finSuccEquiv_X_zero,
    finSuccEquiv_X_succ, AlgEquiv.commutes, Polynomial.algebraMap_apply,
    MvPolynomial.algebraMap_eq]
  have hC : MvPolynomial.finSuccEquiv k n (MvPolynomial.C a)
      = Polynomial.C (MvPolynomial.C a) := by
    have := (MvPolynomial.finSuccEquiv k n).commutes a
    simp only [Polynomial.algebraMap_apply, MvPolynomial.algebraMap_eq] at this
    exact this
  have h (i : Fin n) :
      (Polynomial.C (X (R := k) i) + Polynomial.X ^ ((2 + f.totalDegree) ^ (i.succ : ℕ)))
        ^ v i.succ ≠ 0 := by
    apply pow_ne_zero
    rw [add_comm]
    exact X_pow_add_C_ne_zero (by positivity) _
  rw [hC, natDegree_C_mul (by simpa using ha),
    natDegree_mul (pow_ne_zero _ X_ne_zero) (Finset.prod_ne_zero_iff.mpr fun i _ => h i),
    natDegree_prod _ _ fun i _ => h i]
  simp [Fin.sum_univ_succ, natDegree_pow, add_comm (Polynomial.C _), natDegree_X_pow_add_C,
    mul_comm]
