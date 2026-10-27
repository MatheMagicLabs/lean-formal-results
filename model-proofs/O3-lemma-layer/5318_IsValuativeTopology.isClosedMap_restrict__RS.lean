/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     IsValuativeTopology.isClosedMap_restrict
Source:      Mathlib @ a02a63c2, Mathlib/Topology/Algebra/ValuativeRel/Completion.lean, line 157
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  O3-lemma-layer, arm RS, verified in round 1 (round 0 = first attempt)
Prover:      claude-opus-5-5
Setup:       Opus 5.5 with repair loop: arm R = repair only; arm RS = repair plus the Lean-checked lemma layer
Check:       the proof replaced the human proof in the Mathlib file above; Lean reported
             0 errors and no `sorry`; sorry/admit/native_decide/search tactics were rejected.
-/

open Valuation ValuativeRel IsValuativeTopology UniformSpace MonoidWithZeroHom ValueGroup₀
open Set Filter Topology
variable {R K Γ₀ : Type*}
section Ring
namespace IsValuativeTopology
variable [Ring R] [LinearOrderedCommGroupWithZero Γ₀] (v : Valuation R Γ₀)
open WithZeroTopology
end IsValuativeTopology
end Ring
section DivisionRing
variable [DivisionRing K] [LinearOrderedCommGroupWithZero Γ₀] (v : Valuation K Γ₀)
section InversionEstimate
end InversionEstimate
namespace IsValuativeTopology
variable [ValuativeRel K] [TopologicalSpace K] [IsValuativeTopology K]
section WithZeroTopology
variable [v.Compatible]
open WithZeroTopology

lemma isClosedMap_restrict :
    IsClosedMap (v.restrict : K → v.ValueGroup₀) := by
  intro s hs
  rw [WithZeroTopology.isClosed_iff]
  by_cases h0 : (0 : v.ValueGroup₀) ∈ v.restrict '' s
  · exact Or.inl h0
  right
  have h0' : (0:K) ∉ s := fun h => h0 ⟨0, h, by simp⟩
  have hU : sᶜ ∈ 𝓝 (0:K) := hs.isOpen_compl.mem_nhds h0'
  have key : ∀ x y : K, valuation K x ≤ valuation K y → v x ≤ v y := by
    intro x y h
    first
    | exact (Valuation.Compatible.rel_iff_le (v := v) x y).1
        ((Valuation.Compatible.rel_iff_le (v := valuation K) x y).2 h)
    | exact (Valuation.Compatible.vle_iff_le (v := v) x y).1
        ((Valuation.Compatible.vle_iff_le (v := valuation K) x y).2 h)
    | exact (Valuation.Compatible.rel_iff_le (v := v) x y).1
        (ValuativeRel.valuation_le_valuation.1 h)
  obtain ⟨γ, hγ⟩ := (IsValuativeTopology.mem_nhds_zero_iff _).1 hU
  have hex : ∃ c : K, valuation K c = (γ : ValueGroupWithZero K) := by
    first
    | exact ValuativeRel.valuation_surjective _
    | (obtain ⟨a, b, hab⟩ := ValuativeRel.valuation_surjective (γ : ValueGroupWithZero K)
       exact ⟨a * (b:K)⁻¹, by rw [map_mul, map_inv₀, ← div_eq_mul_inv, hab]⟩)
  obtain ⟨c, hc⟩ := hex
  have hc0 : c ≠ 0 := by
    intro hc0
    rw [hc0, map_zero] at hc
    exact γ.ne_zero hc.symm
  refine ⟨v.restrict c, ?_, ?_⟩
  · simpa using hc0
  · rintro _ ⟨x, hx, rfl⟩
    have h1 : (γ : ValueGroupWithZero K) ≤ valuation K x :=
      not_lt.1 (fun hlt => hγ hlt hx)
    have h2 : v c ≤ v x := key c x (by rw [hc]; exact h1)
    show v.restrict c ≤ v.restrict x
    first
    | (rw [Valuation.restrict_le_iff_le_embedding]; simpa using h2)
    | simpa [Valuation.restrict_le_iff_le_embedding] using h2
