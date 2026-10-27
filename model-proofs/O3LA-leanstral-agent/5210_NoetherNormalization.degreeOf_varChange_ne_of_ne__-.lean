/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     NoetherNormalization.degreeOf_varChange_ne_of_ne
Source:      Mathlib @ a02a63c2, Mathlib/RingTheory/NoetherNormalization.lean, line 118
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  O3LA-leanstral-agent, arm -, verified in final
Prover:      labs-leanstral-1-5
Setup:       Leanstral 1.5 as a tool-using agent (Mistral Vibe)
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

private lemma degreeOf_varChange_ne_of_ne (hv : v ∈ f.support) (hw : w ∈ f.support) (ne : v ≠ w) :
    (varChange f <| monomial v <| f.coeff v).degreeOf 0 ≠
    (varChange f <| monomial w <| f.coeff w).degreeOf 0 := by
  have hvsum (i : Fin (n + 1)) : v i ≤ v.sum fun _ e => e := by
    simpa using Finsupp.single_le_sum v (g := fun _ m => m) (fun _ _ => Nat.zero_le _) i
  have hvlt : ∀ i, v i < up := fun i => by
    apply Nat.lt_of_le_of_lt ((hvsum i).trans (le_totalDegree hv))
    have : up = 2 + f.totalDegree := rfl
    omega
  have hwsum (i : Fin (n + 1)) : w i ≤ w.sum fun _ e => e := by
    simpa using Finsupp.single_le_sum w (g := fun _ m => m) (fun _ _ => Nat.zero_le _) i
  have hwlt : ∀ i, w i < up := fun i => by
    apply Nat.lt_of_le_of_lt ((hwsum i).trans (le_totalDegree hw))
    have : up = 2 + f.totalDegree := rfl
    omega
  have hcoeffv : f.coeff v ≠ 0 := (MvPolynomial.mem_support_iff.mp hv)
  have hcoeffw : f.coeff w ≠ 0 := (MvPolynomial.mem_support_iff.mp hw)
  rw [degreeOf_zero_varChange f v hcoeffv, degreeOf_zero_varChange f w hcoeffw]
  exact sum_r_mul_ne f v w hvlt hwlt ne
