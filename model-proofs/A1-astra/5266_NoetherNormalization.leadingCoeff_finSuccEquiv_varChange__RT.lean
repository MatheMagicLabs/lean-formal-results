/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     NoetherNormalization.leadingCoeff_finSuccEquiv_varChange
Source:      Mathlib @ a02a63c2, Mathlib/RingTheory/NoetherNormalization.lean, line 127
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  A1-astra, arm RT, verified in round 1 (round 0 = first attempt)
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
  have h (i : Fin n) :
      (Polynomial.C (X (R := k) i) +
        Polynomial.X ^ r i.succ).leadingCoeff = 1 := by
    rw [add_comm, leadingCoeff_X_pow_add_C (pow_pos (by omega) _)]
  rw [monomial_eq, Finsupp.prod_pow v fun a ↦ X a]
  simp only [Fin.prod_univ_succ, map_mul, map_prod, map_pow,
    AlgEquiv.ofAlgHom_apply, MvPolynomial.aeval_C, MvPolynomial.aeval_X,
    ite_eq_left, Fin.succ_ne_zero, ite_false, one_smul, map_add,
    finSuccEquiv_X_zero, finSuccEquiv_X_succ]
  simp only [leadingCoeff_mul, leadingCoeff_prod, leadingCoeff_pow, h]
  simp [finSuccEquiv_apply, algebraMap_eq]
