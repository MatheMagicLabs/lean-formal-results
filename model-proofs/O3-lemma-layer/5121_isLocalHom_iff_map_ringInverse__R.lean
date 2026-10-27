/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     isLocalHom_iff_map_ringInverse
Source:      Mathlib @ a02a63c2, Mathlib/Algebra/GroupWithZero/Units/Lemmas.lean, line 44
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

theorem isLocalHom_iff_map_ringInverse [MonoidWithZeroHomClass F M₀ M₀'] [Nontrivial M₀'] (f : F) :
    IsLocalHom f ↔ ∀ a, f a⁻¹ʳ = (f a)⁻¹ʳ := by
  constructor
  · intro hf a
    by_cases ha : IsUnit a
    · obtain ⟨u, rfl⟩ := ha
      have := Ring.inverse_unit (Units.map (f : M₀ →* M₀') u)
      simp only [Units.coe_map, MonoidHom.coe_coe, Units.coe_map_inv] at this
      rw [Ring.inverse_unit, this]
    · have hfa : ¬ IsUnit (f a) := fun h => ha (isUnit_of_map_unit f a h)
      rw [Ring.inverse_non_unit a ha, Ring.inverse_non_unit _ hfa, map_zero]
  · intro h
    refine ⟨fun a ha => ?_⟩
    by_contra hna
    have h1 := Ring.inverse_mul_cancel (f a) ha
    rw [← h, Ring.inverse_non_unit a hna, map_zero, zero_mul] at h1
    exact zero_ne_one h1
