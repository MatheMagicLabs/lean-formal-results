/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     NoetherNormalization.leadingCoeff_finSuccEquiv_varChange
Source:      Mathlib @ a02a63c2, Mathlib/RingTheory/NoetherNormalization.lean, line 127
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  E1-repair-decomposition, arm V, verified in round 1 (round 0 = first attempt)
Prover:      gpt-6-astra
Setup:       GPT-6 Astra, which part of Lean feedback makes repair work: after a shared first attempt (E0), V = full error messages, Z = line numbers only, B = only "Lean rejected this proof"
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
  have hLC (p : MvPolynomial (Fin n) k) (m : ℕ) (hm : 0 < m) :
      (Polynomial.C p + Polynomial.X ^ m).leadingCoeff = 1 := by
    rw [Polynomial.leadingCoeff_add_of_degree_lt]
    · simp
    · apply lt_of_le_of_lt Polynomial.degree_C_le
      simpa using (show (0 : WithBot ℕ) < (m : WithBot ℕ) from
        WithBot.coe_lt_coe.mpr hm)
  have hX (i : Fin (n + 1)) :
      (finSuccEquiv k n (varChange f (MvPolynomial.X i))).leadingCoeff = 1 := by
    refine Fin.cases ?_ (fun i ↦ ?_) i
    · simp [varChange, MvPolynomial.finSuccEquiv]
    · simp [varChange, MvPolynomial.finSuccEquiv, hLC,
        pow_pos (by omega : 0 < 2 + f.totalDegree)]
  simp only [MvPolynomial.monomial_eq, Finsupp.prod, map_mul, map_prod,
    map_pow, Polynomial.leadingCoeff_mul, Polynomial.leadingCoeff_prod,
    Polynomial.leadingCoeff_pow, hX, one_pow, Finset.prod_const_one, mul_one]
  simp [varChange, MvPolynomial.finSuccEquiv]
