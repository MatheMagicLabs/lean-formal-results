/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     NoetherNormalization.degreeOf_varChange_ne_of_ne
Source:      Mathlib @ a02a63c2, Mathlib/RingTheory/NoetherNormalization.lean, line 118
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  O3-lemma-layer, arm R, verified in round 0 (round 0 = first attempt)
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
  have key : ∀ {x : Fin (n+1) →₀ ℕ}, x ∈ f.support → ∀ i, x i < 2 + f.totalDegree :=
    fun hx i =>
      lt_of_le_of_lt ((monomial_le_degreeOf i hx).trans (degreeOf_le_totalDegree f i))
        (by omega)
  first
    | rw [degreeOf_zero_varChange _ _ (mem_support_iff.mp hv),
        degreeOf_zero_varChange _ _ (mem_support_iff.mp hw)]
    | rw [degreeOf_zero_varChange (mem_support_iff.mp hv),
        degreeOf_zero_varChange (mem_support_iff.mp hw)]
    | rw [degreeOf_zero_varChange _ (mem_support_iff.mp hv),
        degreeOf_zero_varChange _ (mem_support_iff.mp hw)]
    | rw [degreeOf_varChange_eq _ _ (mem_support_iff.mp hv),
        degreeOf_varChange_eq _ _ (mem_support_iff.mp hw)]
    | rw [degreeOf_varChange_eq (mem_support_iff.mp hv),
        degreeOf_varChange_eq (mem_support_iff.mp hw)]
  first
    | exact sum_r_mul_ne f w (key hv) (key hw) ne
    | exact sum_r_mul_ne w (key hv) (key hw) ne
    | exact sum_r_mul_ne f v w (key hv) (key hw) ne
    | intro h
      refine ne <| Finsupp.ext <| congrFun <| List.ofFn_inj.mp ?_
      apply Nat.ofDigits_inj_of_len_eq (b := 2 + f.totalDegree) (by omega) (by simp)
      · intro l hl
        obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hl
        exact key hv i
      · intro l hl
        obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hl
        exact key hw i
      · simpa only [Nat.ofDigits_eq_sum_mapIdx, List.mapIdx_eq_ofFn, List.get_ofFn,
          List.length_ofFn, Fin.coe_cast, mul_comm, List.sum_ofFn] using h
