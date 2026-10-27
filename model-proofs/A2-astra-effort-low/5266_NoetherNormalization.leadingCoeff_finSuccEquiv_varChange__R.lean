/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     NoetherNormalization.leadingCoeff_finSuccEquiv_varChange
Source:      Mathlib @ a02a63c2, Mathlib/RingTheory/NoetherNormalization.lean, line 127
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  A2-astra-effort-low, arm R, verified in round 3 (round 0 = first attempt)
Prover:      gpt-6-astra
Setup:       GPT-6 Astra, reasoning effort low (arms R, N0)
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
  classical
  have hmonic (i : Fin (n + 1)) :
      (MvPolynomial.finSuccEquiv k n (varChange f (X i))).Monic := by
    refine Fin.cases ?_ (fun j ↦ ?_) i
    · simpa [varChange, MvPolynomial.finSuccEquiv] using
        (Polynomial.monic_X : (Polynomial.X :
          Polynomial (MvPolynomial (Fin n) k)).Monic)
    · have hp : 0 < (2 + f.totalDegree) ^ (j.val + 1) := by
        positivity
      simp [varChange, MvPolynomial.finSuccEquiv]
      monicity <;> simp_all <;> omega
  have hlc (i : Fin (n + 1)) :
      (MvPolynomial.finSuccEquiv k n (varChange f (X i))).leadingCoeff = 1 :=
    (hmonic i).leadingCoeff
  have hc (a : k) :
      MvPolynomial.finSuccEquiv k n (varChange f (MvPolynomial.C a)) =
        Polynomial.C (MvPolynomial.C a) := by
    simp [varChange, MvPolynomial.finSuccEquiv]
  rw [MvPolynomial.monomial_eq]
  simp only [Finsupp.prod, map_mul, map_prod, map_pow, hc,
    Polynomial.leadingCoeff_mul, Polynomial.leadingCoeff_prod,
    Polynomial.leadingCoeff_pow, Polynomial.leadingCoeff_C, hlc,
    one_pow, Finset.prod_const_one, mul_one]
  rfl
