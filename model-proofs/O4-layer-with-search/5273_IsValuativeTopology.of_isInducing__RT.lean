/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     IsValuativeTopology.of_isInducing
Source:      Mathlib @ a02a63c2, Mathlib/Topology/Algebra/ValuativeRel/ValuativeTopology.lean, line 237
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  O4-layer-with-search, arm RT, verified in round 2 (round 0 = first attempt)
Prover:      claude-opus-5-5
Setup:       Opus 5.5 with repair loop, lemma layer and name search (arm RT)
Check:       the proof replaced the human proof in the Mathlib file above; Lean reported
             0 errors and no `sorry`; sorry/admit/native_decide/search tactics were rejected.
-/

open scoped Topology Uniformity
open Set Filter Valuation ValuativeRel MonoidWithZeroHom ValueGroup₀ ValueGroupWithZero
noncomputable section
variable (R : Type*) [Ring R] [ValuativeRel R]
variable {R} in
namespace ValuativeRel
local instance topologicalSpace : TopologicalSpace R := (valuation R).subgroups_basis.topology
local instance uniformSpace : UniformSpace R := IsTopologicalAddGroup.rightUniformSpace R
local instance isUniformAddGroup : IsUniformAddGroup R := isUniformAddGroup_of_addCommGroup
end ValuativeRel
variable {R}
variable {K : Type*} [DivisionRing K] [ValuativeRel K] {Γ₀ : Type*}
section TopologicalSpace
variable [TopologicalSpace R] (v : Valuation R Γ₀) [v.Compatible]
namespace IsValuativeTopology
open scoped Pointwise in
variable [IsValuativeTopology R]
variable (R) in
variable (R) in
end IsValuativeTopology
open IsValuativeTopology
variable [IsValuativeTopology R]
namespace Valuation
end Valuation
namespace IsValuativeTopology
variable (R) in
end IsValuativeTopology
end TopologicalSpace
section IsInducing
namespace IsValuativeTopology
variable [TopologicalSpace R]
variable {S : Type*} [Ring S] [ValuativeRel S] [TopologicalSpace S] [IsValuativeTopology S]
open ValuativeRel Topology in

theorem of_isInducing {F : Type*} [FunLike F R S] [RingHomClass F R S] {f : F}
    (hsurj : Function.Surjective f) (hf : IsInducing f) (hv : ∀ a b, f a ≤ᵥ f b ↔ a ≤ᵥ b) :
    IsValuativeTopology R where
  mem_nhds_iff {s x} := by
    have hR : ∀ a b : R, a ≤ᵥ b ↔ valuation R a ≤ valuation R b := fun a b => by
      first
        | exact Valuation.Compatible.vle_iff_le a b
        | exact Valuation.Compatible.rel_iff_le a b
        | exact (Valuation.Compatible.vle_iff_le (v := valuation R) a b)
        | exact (Valuation.Compatible.rel_iff_le (v := valuation R) a b)
    have hS : ∀ a b : S, a ≤ᵥ b ↔ valuation S a ≤ valuation S b := fun a b => by
      first
        | exact Valuation.Compatible.vle_iff_le a b
        | exact Valuation.Compatible.rel_iff_le a b
        | exact (Valuation.Compatible.vle_iff_le (v := valuation S) a b)
        | exact (Valuation.Compatible.rel_iff_le (v := valuation S) a b)
    have hz0R : ∀ c : R, valuation R c = 0 ↔ c ≤ᵥ 0 := by
      intro c; rw [hR, _root_.map_zero, le_zero_iff]
    have hz0S : ∀ c : S, valuation S c = 0 ↔ c ≤ᵥ 0 := by
      intro c; rw [hS, _root_.map_zero, le_zero_iff]
    have hLR : ∀ z a b : R, valuation R b ≠ 0 →
        (valuation R z < valuation R a / valuation R b ↔ ¬ a ≤ᵥ z * b) := by
      intro z a b hb
      rw [lt_div_iff₀ (zero_lt_iff.mpr hb), ← _root_.map_mul, hR, not_le]
    have hLS : ∀ z a b : S, valuation S b ≠ 0 →
        (valuation S z < valuation S a / valuation S b ↔ ¬ a ≤ᵥ z * b) := by
      intro z a b hb
      rw [lt_div_iff₀ (zero_lt_iff.mpr hb), ← _root_.map_mul, hS, not_le]
    have hne : ∀ c : R, valuation R c ≠ 0 ↔ valuation S (f c) ≠ 0 := by
      intro c
      rw [ne_eq, ne_eq, hz0R, hz0S, ← _root_.map_zero f, hv]
    suffices H : s ∈ 𝓝 x ↔ ∃ γ : (ValueGroupWithZero R)ˣ,
        {z | valuation R (z - x) < γ} ⊆ s by
      first
        | exact H
        | (rw [H]; constructor <;> rintro ⟨γ, hγ⟩ <;> refine ⟨γ, ?_⟩
           · rintro _ ⟨z, hz, rfl⟩; apply hγ; simpa using hz
           · intro z hz
             have := hγ (Set.mem_image_of_mem (x + ·)
               (show z - x ∈ {z | valuation R z < ↑γ} from hz))
             simpa using this)
    rw [hf.nhds_eq_comap, Filter.mem_comap]
    constructor
    · rintro ⟨t, ht, hts⟩
      obtain ⟨δ, hδ⟩ := (IsValuativeTopology.mem_nhds_iff' (R := S)).mp ht
      obtain ⟨a', b', hab⟩ :=
        ValuativeRel.exists_valuation_div_valuation_eq (δ : ValueGroupWithZero S)
      obtain ⟨a, rfl⟩ := hsurj a'
      obtain ⟨b, hb⟩ := hsurj (b' : S)
      rw [← hb] at hab
      have hbS : valuation S (f b) ≠ 0 := by
        intro h; apply δ.ne_zero; rw [← hab, h, div_zero]
      have haS : valuation S (f a) ≠ 0 := by
        intro h; apply δ.ne_zero; rw [← hab, h, zero_div]
      have hbR : valuation R b ≠ 0 := (hne b).mpr hbS
      have haR : valuation R a ≠ 0 := (hne a).mpr haS
      refine ⟨Units.mk0 (valuation R a / valuation R b) (div_ne_zero haR hbR), ?_⟩
      intro z hz
      apply hts
      apply hδ
      have hz' : valuation R (z - x) < valuation R a / valuation R b := by
        simpa only [Set.mem_setOf_eq, Units.val_mk0] using hz
      rw [hLR _ _ _ hbR] at hz'
      show valuation S (f z - f x) < (δ : ValueGroupWithZero S)
      rw [← hab, ← _root_.map_sub f, hLS _ _ _ hbS, ← _root_.map_mul f, hv]
      exact hz'
    · rintro ⟨γ, hγ⟩
      obtain ⟨a, b', hab⟩ :=
        ValuativeRel.exists_valuation_div_valuation_eq (γ : ValueGroupWithZero R)
      have hbR : valuation R (b' : R) ≠ 0 := by
        intro h; apply γ.ne_zero; rw [← hab, h, div_zero]
      have haR : valuation R a ≠ 0 := by
        intro h; apply γ.ne_zero; rw [← hab, h, zero_div]
      have hbS := (hne _).mp hbR
      have haS := (hne _).mp haR
      refine ⟨{w | valuation S (w - f x) <
          (Units.mk0 (valuation S (f a) / valuation S (f b')) (div_ne_zero haS hbS) :
            ValueGroupWithZero S)}, ?_, ?_⟩
      · exact (IsValuativeTopology.mem_nhds_iff' (R := S)).mpr ⟨_, subset_rfl⟩
      · intro z hz
        apply hγ
        have hz' : valuation S (f z - f x) < valuation S (f a) / valuation S (f b') := by
          simpa only [Set.mem_preimage, Set.mem_setOf_eq, Units.val_mk0] using hz
        rw [← _root_.map_sub f, hLS _ _ _ hbS, ← _root_.map_mul f, hv] at hz'
        show valuation R (z - x) < (γ : ValueGroupWithZero R)
        rw [← hab, hLR _ _ _ hbR]
        exact hz'
