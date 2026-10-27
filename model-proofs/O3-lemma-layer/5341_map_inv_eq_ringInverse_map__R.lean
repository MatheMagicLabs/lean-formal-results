/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     map_inv_eq_ringInverse_map
Source:      Mathlib @ a02a63c2, Mathlib/Algebra/GroupWithZero/Units/Lemmas.lean, line 72
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  O3-lemma-layer, arm R, verified in round 0 (round 0 = first attempt)
Prover:      claude-opus-5-5
Setup:       Opus 5.5 with repair loop: arm R = repair only; arm RS = repair plus the Lean-checked lemma layer
Check:       the proof replaced the human proof in the Mathlib file above; Lean reported
             0 errors and no `sorry`; sorry/admit/native_decide/search tactics were rejected.
-/

open scoped Ring
variable {M M₀ G₀ M₀' G₀' F F' : Type*}
variable [MonoidWithZero M₀]
section MonoidWithZero
variable [MonoidWithZero M₀'] [FunLike F M₀ M₀']
end MonoidWithZero
section Monoid
variable [Monoid M] [GroupWithZero G₀]

theorem map_inv_eq_ringInverse_map [FunLike F G₀ M₀]
    [MonoidWithZeroHomClass F G₀ M₀] (f : F) (a : G₀) :
    f a⁻¹ = (f a)⁻¹ʳ := by
  by_cases h : a = 0
  · subst h
    simp [Ring.inverse_zero]
  · have hu : IsUnit (f a) := (IsUnit.mk0 a h).map f
    have h1 : f a⁻¹ * f a = 1 := by
      rw [← map_mul, inv_mul_cancel₀ h, map_one]
    calc f a⁻¹ = f a⁻¹ * (f a * (f a)⁻¹ʳ) := by
          rw [Ring.mul_inverse_cancel _ hu, mul_one]
      _ = (f a)⁻¹ʳ := by rw [← mul_assoc, h1, one_mul]
