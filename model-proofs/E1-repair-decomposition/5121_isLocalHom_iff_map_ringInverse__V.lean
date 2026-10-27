/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     isLocalHom_iff_map_ringInverse
Source:      Mathlib @ a02a63c2, Mathlib/Algebra/GroupWithZero/Units/Lemmas.lean, line 44
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  E1-repair-decomposition, arm V, verified in round 1 (round 0 = first attempt)
Prover:      gpt-6-astra
Setup:       GPT-6 Astra, which part of Lean feedback makes repair work: after a shared first attempt (E0), V = full error messages, Z = line numbers only, B = only "Lean rejected this proof"
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
  classical
  have map_inverse_of_unit (a : M₀) (ha : IsUnit a) :
      f a⁻¹ʳ = (f a)⁻¹ʳ := by
    rcases ha with ⟨u, rfl⟩
    let g : M₀ →* M₀' :=
      { toFun := f
        map_one' := map_one f
        map_mul' := map_mul f }
    let v : M₀'ˣ := Units.map g u
    change f (↑u : M₀)⁻¹ʳ = (↑v : M₀')⁻¹ʳ
    simp only [Ring.inverse_unit]
    rfl
  constructor
  · rintro ⟨h⟩ a
    by_cases ha : IsUnit a
    · exact map_inverse_of_unit a ha
    · have hb : ¬ IsUnit (f a) := fun hb => ha (h a hb)
      rw [Ring.inverse_non_unit a ha, Ring.inverse_non_unit (f a) hb, map_zero]
  · intro h
    constructor
    intro a ha
    by_contra hn
    have hz : (f a)⁻¹ʳ = 0 := by
      rw [← h a, Ring.inverse_non_unit a hn, map_zero]
    rcases ha with ⟨u, hu⟩
    rw [← hu, Ring.inverse_unit] at hz
    exact (Units.ne_zero (u⁻¹)) hz
