/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     NoetherNormalization.leadingCoeff_finSuccEquiv_varChange
Source:      Mathlib @ a02a63c2, Mathlib/RingTheory/NoetherNormalization.lean, line 127
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  A2-astra-effort-high, arm R, verified in round 3 (round 0 = first attempt)
Prover:      gpt-6-astra
Setup:       GPT-6 Astra, reasoning effort high (arms R, N0)
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
  have hpos (j : ℕ) : 0 < (2 + f.totalDegree) ^ j :=
    pow_pos (by omega) _
  have h₁ (a : MvPolynomial (Fin n) k) (d : ℕ) (hd : 0 < d) :
      (Polynomial.C a + Polynomial.X ^ d).leadingCoeff = 1 := by
    rw [Polynomial.leadingCoeff_add_of_degree_lt]
    · simp
    · apply lt_of_le_of_lt Polynomial.degree_C_le
      rw [Polynomial.degree_X_pow]
      exact_mod_cast hd
  have h₂ (a : MvPolynomial (Fin n) k) (d : ℕ) (hd : 0 < d) :
      (Polynomial.X ^ d + Polynomial.C a).leadingCoeff = 1 := by
    rw [add_comm]
    exact h₁ a d hd
  have hX (i : Fin (n + 1)) :
      (finSuccEquiv k n (varChange f (MvPolynomial.X i))).leadingCoeff = 1 := by
    cases i using Fin.cases <;>
      simp [varChange, MvPolynomial.finSuccEquiv, h₁, h₂, hpos]
  have hC (a : k) :
      finSuccEquiv k n (varChange f (MvPolynomial.C a)) =
        Polynomial.C (MvPolynomial.C a) := by
    simp [varChange, MvPolynomial.finSuccEquiv]
  have hprod (s : Finset (Fin (n + 1)))
      (p : Fin (n + 1) → Polynomial (MvPolynomial (Fin n) k)) :
      (∏ i ∈ s, p i).leadingCoeff = ∏ i ∈ s, (p i).leadingCoeff := by
    induction s using Finset.induction_on with
    | empty => simp
    | @insert i s hi ih =>
        simp [hi, Polynomial.leadingCoeff_mul, ih]
  rw [MvPolynomial.monomial_eq]
  simp only [Finsupp.prod, map_mul, map_prod, map_pow]
  rw [Polynomial.leadingCoeff_mul, hC, Polynomial.leadingCoeff_C, hprod]
  simp only [Polynomial.leadingCoeff_pow, hX, one_pow,
    Finset.prod_const_one, mul_one]
  rfl
