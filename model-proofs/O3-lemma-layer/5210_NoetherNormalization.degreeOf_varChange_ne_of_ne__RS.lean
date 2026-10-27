/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     NoetherNormalization.degreeOf_varChange_ne_of_ne
Source:      Mathlib @ a02a63c2, Mathlib/RingTheory/NoetherNormalization.lean, line 118
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  O3-lemma-layer, arm RS, verified in round 0 (round 0 = first attempt)
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

private lemma degreeOf_varChange_ne_of_ne (hv : v ∈ f.support) (hw : w ∈ f.support) (ne : v ≠ w) :
    (varChange f <| monomial v <| f.coeff v).degreeOf 0 ≠
    (varChange f <| monomial w <| f.coeff w).degreeOf 0 := by
  have hv0 : f.coeff v ≠ 0 := mem_support_iff.mp hv
  have hw0 : f.coeff w ≠ 0 := mem_support_iff.mp hw
  rw [degreeOf_zero_varChange (f := f) (v := v) (ha := hv0),
    degreeOf_zero_varChange (f := f) (v := w) (ha := hw0)]
  refine sum_r_mul_ne (vlt := fun i => ?_) (wlt := fun i => ?_) (ne := ne)
  · have := (monomial_le_degreeOf i hv).trans (degreeOf_le_totalDegree f i)
    omega
  · have := (monomial_le_degreeOf i hw).trans (degreeOf_le_totalDegree f i)
    omega
