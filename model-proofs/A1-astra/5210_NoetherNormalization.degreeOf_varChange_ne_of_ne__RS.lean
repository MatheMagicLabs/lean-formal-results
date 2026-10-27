/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     NoetherNormalization.degreeOf_varChange_ne_of_ne
Source:      Mathlib @ a02a63c2, Mathlib/RingTheory/NoetherNormalization.lean, line 118
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  A1-astra, arm RS, verified in round 0 (round 0 = first attempt)
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

private lemma degreeOf_varChange_ne_of_ne (hv : v ∈ f.support) (hw : w ∈ f.support) (ne : v ≠ w) :
    (varChange f <| monomial v <| f.coeff v).degreeOf 0 ≠
    (varChange f <| monomial w <| f.coeff w).degreeOf 0 := by
  classical
  have hbound : ∀ d ∈ f.support, ∀ i, d i < 2 + f.totalDegree := by
    intro d hd i
    have hsum : d.sum (fun _ e => e) ≤ f.totalDegree :=
      Finset.le_sup (f := fun d => d.sum (fun _ e => e)) hd
    have hi : d i ≤ d.sum (fun _ e => e) := by
      by_cases h : d i = 0
      · simp [h]
      · exact Finset.single_le_sum (fun j _ => Nat.zero_le (d j))
          (Finsupp.mem_support_iff.mpr h)
    omega
  rw [degreeOf_zero_varChange (f := f) (v := v)
        (MvPolynomial.mem_support_iff.mp hv),
      degreeOf_zero_varChange (f := f) (v := w)
        (MvPolynomial.mem_support_iff.mp hw)]
  exact sum_r_mul_ne (f := f) (v := v) (w := w)
    (hbound v hv) (hbound w hw) ne
