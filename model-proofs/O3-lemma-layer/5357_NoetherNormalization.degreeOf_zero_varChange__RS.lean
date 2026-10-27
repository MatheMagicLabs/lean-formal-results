/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     NoetherNormalization.degreeOf_zero_varChange
Source:      Mathlib @ a02a63c2, Mathlib/RingTheory/NoetherNormalization.lean, line 100
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  O3-lemma-layer, arm RS, verified in round 1 (round 0 = first attempt)
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
  have h : ∀ i, (finSuccEquiv k n (varChange f (X i))).natDegree = r i := by
    intro i
    by_cases hi : i = 0
    · subst hi
      simp [varChange, finSuccEquiv_X_zero]
    · obtain ⟨j, rfl⟩ := Fin.exists_succ_eq.mpr hi
      simp [varChange, finSuccEquiv_X_succ, finSuccEquiv_X_zero,
        Polynomial.natDegree_C_add, Polynomial.natDegree_X_pow]
  have h0 : ∀ i, finSuccEquiv k n (varChange f (X i)) ≠ 0 := by
    intro i
    apply Polynomial.ne_zero_of_natDegree_gt (n := 0)
    rw [h i]
    positivity
  have hCa : finSuccEquiv k n (varChange f (MvPolynomial.C a))
      = Polynomial.C (MvPolynomial.C a) := by
    simp [varChange, finSuccEquiv_apply, MvPolynomial.algebraMap_eq]
  have hCa0 : (MvPolynomial.C a : MvPolynomial (Fin n) k) ≠ 0 := by simpa using ha
  rw [← natDegree_finSuccEquiv, monomial_eq,
    Finsupp.prod_fintype _ _ (fun i => pow_zero _)]
  simp only [map_mul, map_prod, map_pow]
  rw [hCa, Polynomial.natDegree_C_mul hCa0,
    Polynomial.natDegree_prod _ _ (fun i _ => pow_ne_zero _ (h0 i))]
  simp only [Polynomial.natDegree_pow, h]
  exact Finset.sum_congr rfl fun i _ => mul_comm _ _
