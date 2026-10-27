/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     isLocalHom_iff_map_ringInverse
Source:      Mathlib @ a02a63c2, Mathlib/Algebra/GroupWithZero/Units/Lemmas.lean, line 44
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  A2-astra-effort-low, arm R, verified in round 1 (round 0 = first attempt)
Prover:      gpt-6-astra
Setup:       GPT-6 Astra, reasoning effort low (arms R, N0)
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
  · intro hf
    letI : IsLocalHom f := hf
    intro a
    exact map_ringInverse f a
  · intro h
    constructor
    intro a ha
    by_contra hn
    have hz : (f a)⁻¹ʳ = 0 := by
      rw [← h a]
      simp [Ring.inverse, hn]
    have hu : (↑(ha.unit⁻¹) : M₀') = 0 := by
      simpa only [Ring.inverse, dif_pos ha] using hz
    exact Units.ne_zero (ha.unit⁻¹) hu
