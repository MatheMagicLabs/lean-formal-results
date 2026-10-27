/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     NoetherNormalization.leadingCoeff_finSuccEquiv_varChange
Source:      Mathlib @ a02a63c2, Mathlib/RingTheory/NoetherNormalization.lean, line 127
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  A1-astra, arm RS, verified in round 2 (round 0 = first attempt)
Prover:      gpt-6-astra
Setup:       GPT-6 Astra (Codex, effort medium): R = proof plus up to 3 repair rounds with Lean errors; RS = R plus lemma layer; RT = R with read-only Mathlib sources to search; N0-N3 = independent attempts
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

private lemma leadingCoeff_finSuccEquiv_varChange :
    (finSuccEquiv k n <| varChange f <| monomial v <| f.coeff v).leadingCoeff =
    algebraMap k _ (f.coeff v) := by
  have hp (j : ℕ) : 0 < (2 + f.totalDegree) ^ j :=
    pow_pos (by omega) _
  have h (i : Fin (n + 1)) :
      (finSuccEquiv k n (varChange f (MvPolynomial.X i))).leadingCoeff = 1 := by
    cases i using Fin.cases with
    | zero =>
      simp [varChange, MvPolynomial.finSuccEquiv_X_zero]
    | succ i =>
      simp [varChange, MvPolynomial.finSuccEquiv_X_zero,
        MvPolynomial.finSuccEquiv_X_succ]
      rw [Polynomial.leadingCoeff_add_of_degree_lt]
      · simp
      · apply lt_of_le_of_lt Polynomial.degree_C_le
        rw [Polynomial.degree_X_pow]
        exact_mod_cast hp (i.val + 1)
  rw [MvPolynomial.monomial_eq]
  simp only [Finsupp.prod, map_mul, map_prod, map_pow,
    Polynomial.leadingCoeff_mul, Polynomial.leadingCoeff_prod,
    Polynomial.leadingCoeff_pow]
  simp only [h, one_pow, Finset.prod_const_one, mul_one]
  simp [varChange, MvPolynomial.finSuccEquiv_apply]
