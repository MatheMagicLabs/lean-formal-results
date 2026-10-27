/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     IsValuativeTopology.isClosedMap_restrict
Source:      Mathlib @ a02a63c2, Mathlib/Topology/Algebra/ValuativeRel/Completion.lean, line 157
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  O3-lemma-layer, arm R, verified in round 2 (round 0 = first attempt)
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
  intro C hC
  rw [WithZeroTopology.isClosed_iff]
  by_cases h0 : (0 : K) ∈ C
  · left
    exact ⟨0, h0, by simp⟩
  · have hC' : Cᶜ ∈ 𝓝 (0 : K) := hC.isOpen_compl.mem_nhds h0
    obtain ⟨γ, hγ⟩ := (IsValuativeTopology.mem_nhds_zero_iff _).mp hC'
    obtain ⟨x, y, hxy⟩ :=
      ValuativeRel.exists_valuation_div_valuation_eq (γ : ValueGroupWithZero K)
    have hy : (y : K) ≠ 0 := by
      intro h
      rw [h, map_zero, div_zero] at hxy
      exact γ.ne_zero hxy.symm
    have hx : x ≠ 0 := by
      intro h
      rw [h, map_zero, zero_div] at hxy
      exact γ.ne_zero hxy.symm
    set a := x / (y : K) with ha_def
    have ha : a ≠ 0 := div_ne_zero hx hy
    have hva : valuation K a = γ := by
      rw [ha_def, map_div₀, hxy]
    have hne : v.restrict a ≠ 0 := by
      first
        | simpa using ha
        | exact (map_ne_zero _).mpr ha
        | simp [ha]
    have hle : ∀ z ∈ v.restrict '' C, v.restrict a ≤ z := by
      rintro _ ⟨c, hc, rfl⟩
      have h1 : ¬ valuation K c < valuation K a := by
        intro h
        rw [hva] at h
        exact hγ h hc
      have h3 : valuation K a ≤ valuation K c := not_lt.mp h1
      have h2 : v a ≤ v c := by
        first
          | exact (Valuation.Compatible.vle_iff_le (v := v) a c).mp
              ((Valuation.Compatible.vle_iff_le (v := valuation K) a c).mpr h3)
          | exact (Valuation.Compatible.vle_iff_le (v := v)).mp
              ((Valuation.Compatible.vle_iff_le (v := valuation K)).mpr h3)
          | exact (Valuation.Compatible.rel_iff_le (v := v) a c).mp
              ((Valuation.Compatible.rel_iff_le (v := valuation K) a c).mpr h3)
          | exact (Valuation.Compatible.vle_iff_le (v := v) a c).mp
              ((ValuativeRel.valuation_le_valuation).mp h3)
          | exact (Valuation.Compatible.vle_iff_le (v := v) a c).mp
              ((ValuativeRel.valuation_le_valuation).mpr h3)
      show v.restrict a ≤ v.restrict c
      first
        | exact (Valuation.restrict_le_iff v).mpr h2
        | exact (v.restrict_le_iff).mpr h2
        | simpa [Valuation.restrict_le_iff] using h2
        | simpa [Valuation.restrict] using h2
        | simpa using h2
    first
      | exact Or.inr ⟨v.restrict a, hne, hle⟩
      | exact Or.inr ⟨Units.mk0 _ hne, hle⟩
      | exact Or.inr ⟨Units.mk0 _ hne, fun z hz => hle z hz⟩
      | exact Or.inr ⟨v.restrict a, hne, fun z hz => hle z hz⟩
      | exact Or.inr ⟨v.restrict a, fun z hz => hle z hz, hne⟩
      | exact Or.inr ⟨Units.mk0 _ hne, fun z hz => Set.mem_Ici.mpr (hle z hz)⟩
