/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     NoetherNormalization.degreeOf_varChange_ne_of_ne
Source:      Mathlib @ a02a63c2, Mathlib/RingTheory/NoetherNormalization.lean, line 118
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  O3LA3-leanstral-agent-feedback, arm rueck, verified in final
Prover:      labs-leanstral-1-5
Setup:       Leanstral 1.5 agent with goal-state feedback (arm rueck)
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
  have hv_coeff : f.coeff v ≠ 0 := (MvPolynomial.mem_support_iff.mp hv)
  have hw_coeff : f.coeff w ≠ 0 := (MvPolynomial.mem_support_iff.mp hw)
  have hv_lt : ∀ i, v i < up := by
    intro i
    have hsum := MvPolynomial.le_totalDegree hv
    have hle : v i ≤ v.sum (fun _ e => e) := by
      by_cases hi : v i = 0
      · rw [hi]; exact Nat.zero_le _
      · have hi_mem : i ∈ v.support := Finsupp.mem_support_iff.mpr hi
        have h := Finset.single_le_sum (fun j hj => Nat.zero_le (v j)) hi_mem
        simpa [Finsupp.sum] using h
    have h_total_lt : f.totalDegree < 2 + f.totalDegree := by
      nlinarith
    exact Nat.lt_of_le_of_lt (Nat.le_trans hle hsum) h_total_lt
  have hw_lt : ∀ i, w i < up := by
    intro i
    have hsum := MvPolynomial.le_totalDegree hw
    have hle : w i ≤ w.sum (fun _ e => e) := by
      by_cases hi : w i = 0
      · rw [hi]; exact Nat.zero_le _
      · have hi_mem : i ∈ w.support := Finsupp.mem_support_iff.mpr hi
        have h := Finset.single_le_sum (fun j hj => Nat.zero_le (w j)) hi_mem
        simpa [Finsupp.sum] using h
    have h_total_lt : f.totalDegree < 2 + f.totalDegree := by
      nlinarith
    exact Nat.lt_of_le_of_lt (Nat.le_trans hle hsum) h_total_lt
  have h1 : (varChange f <| monomial v <| f.coeff v).degreeOf 0 = ∑ x : Fin (n + 1), r x * v x :=
    degreeOf_zero_varChange f v hv_coeff
  have h2 : (varChange f <| monomial w <| f.coeff w).degreeOf 0 = ∑ x : Fin (n + 1), r x * w x :=
    degreeOf_zero_varChange f w hw_coeff
  rw [h1, h2]
  exact sum_r_mul_ne f v w hv_lt hw_lt ne
