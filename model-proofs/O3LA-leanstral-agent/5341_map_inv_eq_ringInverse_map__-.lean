/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     map_inv_eq_ringInverse_map
Source:      Mathlib @ a02a63c2, Mathlib/Algebra/GroupWithZero/Units/Lemmas.lean, line 72
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  O3LA-leanstral-agent, arm -, verified in final
Prover:      labs-leanstral-1-5
Setup:       Leanstral 1.5 as a tool-using agent (Mistral Vibe)
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
  rcases em (IsUnit a) with (h | h)
  · rw [← Ring.inverse_eq_inv a]
    exact h.map_ringInverse f
  · rw [not_ne_iff.mp (isUnit_iff_ne_zero.not.mp h), inv_zero, map_zero, Ring.inverse_zero]
