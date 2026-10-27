/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     NoetherNormalization.leadingCoeff_finSuccEquiv_varChange
Source:      Mathlib @ a02a63c2, Mathlib/RingTheory/NoetherNormalization.lean, line 127
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

private lemma leadingCoeff_finSuccEquiv_varChange :
    (finSuccEquiv k n <| varChange f <| monomial v <| f.coeff v).leadingCoeff =
    algebraMap k _ (f.coeff v) := by
  rw [monomial_eq, Finsupp.prod_fintype _ _ (fun i ↦ pow_zero _)]
  simp only [map_mul, map_prod, map_pow, leadingCoeff_mul, leadingCoeff_prod,
    leadingCoeff_pow]
  have h1 : ∀ j, ((finSuccEquiv k n) ((varChange f) (X j))).leadingCoeff = 1 := fun j ↦ by
    by_cases h : j = 0
    · subst h
      simp [varChange, T1, MvPolynomial.finSuccEquiv_X_zero]
    · obtain ⟨i, rfl⟩ := Fin.exists_succ_eq.mpr h
      simp only [varChange, T1, AlgEquiv.ofAlgHom_apply, MvPolynomial.aeval_X, if_neg h,
        one_smul, map_add, map_pow, MvPolynomial.finSuccEquiv_X_succ,
        MvPolynomial.finSuccEquiv_X_zero]
      rw [add_comm, leadingCoeff_X_pow_add_C (by positivity)]
  have h2 : ((finSuccEquiv k n) ((varChange f) (C (f.coeff v)))).leadingCoeff =
      algebraMap k _ (f.coeff v) := by
    rw [← MvPolynomial.algebraMap_eq, AlgEquiv.commutes, AlgEquiv.commutes,
      Polynomial.algebraMap_apply, Polynomial.leadingCoeff_C]
  rw [h2, Finset.prod_eq_one (fun j _ ↦ by rw [h1, one_pow]), mul_one]
