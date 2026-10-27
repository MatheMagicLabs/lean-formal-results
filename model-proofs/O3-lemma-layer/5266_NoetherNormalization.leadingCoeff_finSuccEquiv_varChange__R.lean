/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     NoetherNormalization.leadingCoeff_finSuccEquiv_varChange
Source:      Mathlib @ a02a63c2, Mathlib/RingTheory/NoetherNormalization.lean, line 127
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

private lemma leadingCoeff_finSuccEquiv_varChange :
    (finSuccEquiv k n <| varChange f <| monomial v <| f.coeff v).leadingCoeff =
    algebraMap k _ (f.coeff v) := by
  rw [monomial_eq, Finsupp.prod_fintype _ _ (fun i => pow_zero _)]
  rw [map_mul, map_mul, leadingCoeff_mul, map_prod, map_prod, leadingCoeff_prod]
  rw [Finset.prod_eq_one, mul_one]
  · rw [← MvPolynomial.algebraMap_eq, AlgEquiv.commutes, AlgEquiv.commutes,
      Polynomial.algebraMap_apply, leadingCoeff_C]
  · intro i _
    rw [map_pow, map_pow, leadingCoeff_pow]
    convert one_pow (v i)
    cases i using Fin.cases with
    | zero =>
      simp [varChange, T1, AlgEquiv.ofAlgHom_apply, MvPolynomial.aeval_X,
        finSuccEquiv_X_zero]
    | succ j =>
      simp only [varChange, T1, AlgEquiv.ofAlgHom_apply, MvPolynomial.aeval_X,
        Fin.succ_ne_zero, if_false, ↓reduceIte, one_smul, map_add, map_pow,
        finSuccEquiv_X_succ, finSuccEquiv_X_zero]
      first
        | (rw [add_comm]; exact leadingCoeff_X_pow_add_C (by positivity))
        | simp [add_comm]
