/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     IsValuativeTopology.of_isInducing
Source:      Mathlib @ a02a63c2, Mathlib/Topology/Algebra/ValuativeRel/ValuativeTopology.lean, line 237
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  O3-lemma-layer, arm R, verified in round 3 (round 0 = first attempt)
Prover:      claude-opus-5-5
Setup:       Opus 5.5 with repair loop: arm R = repair only; arm RS = repair plus the Lean-checked lemma layer
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
    have cR : ∀ x y : R, x ≤ᵥ y ↔ valuation R x ≤ valuation R y := by
      intro x y
      first
      | exact Valuation.Compatible.vle_iff_le (v := valuation R) x y
      | exact Valuation.Compatible.vle_iff_le x y
      | exact (ValuativeRel.valuation_le_valuation (R := R)).symm
      | exact ValuativeRel.valuation_le_valuation.symm
      | simp [ValuativeRel.valuation_le_valuation]
      | simp
    have cS : ∀ x y : S, x ≤ᵥ y ↔ valuation S x ≤ valuation S y := by
      intro x y
      first
      | exact Valuation.Compatible.vle_iff_le (v := valuation S) x y
      | exact Valuation.Compatible.vle_iff_le x y
      | exact (ValuativeRel.valuation_le_valuation (R := S)).symm
      | exact ValuativeRel.valuation_le_valuation.symm
      | simp [ValuativeRel.valuation_le_valuation]
      | simp
    have hzR : ∀ r : R, valuation R r = 0 ↔ r ≤ᵥ 0 := by
      intro r
      rw [cR, map_zero]
      exact ⟨fun h => h.le, fun h => le_antisymm h zero_le'⟩
    have hzS : ∀ r : S, valuation S r = 0 ↔ r ≤ᵥ 0 := by
      intro r
      rw [cS, map_zero]
      exact ⟨fun h => h.le, fun h => le_antisymm h zero_le'⟩
    have surjR : ∀ γ : ValueGroupWithZero R, ∃ a b : R, valuation R b ≠ 0 ∧
        valuation R a / valuation R b = γ := by
      intro γ
      first
      | (obtain ⟨a, b, h⟩ := ValuativeRel.exists_valuation_div_valuation_eq γ
         refine ⟨a, b, ?_, h⟩
         first
         | exact fun h0 => b.2 ((hzR _).mp h0)
         | exact ValuativeRel.valuation_posSubmonoid_ne_zero b)
      | (induction γ using ValuativeRel.ValueGroupWithZero.ind with
         | mk x y =>
           refine ⟨x, y, ?_, (ValuativeRel.ValueGroupWithZero.mk_eq_div x y).symm⟩
           first
           | exact fun h0 => y.2 ((hzR _).mp h0)
           | exact ValuativeRel.valuation_posSubmonoid_ne_zero y)
    have surjS : ∀ γ : ValueGroupWithZero S, ∃ a b : S, valuation S b ≠ 0 ∧
        valuation S a / valuation S b = γ := by
      intro γ
      first
      | (obtain ⟨a, b, h⟩ := ValuativeRel.exists_valuation_div_valuation_eq γ
         refine ⟨a, b, ?_, h⟩
         first
         | exact fun h0 => b.2 ((hzS _).mp h0)
         | exact ValuativeRel.valuation_posSubmonoid_ne_zero b)
      | (induction γ using ValuativeRel.ValueGroupWithZero.ind with
         | mk x y =>
           refine ⟨x, y, ?_, (ValuativeRel.ValueGroupWithZero.mk_eq_div x y).symm⟩
           first
           | exact fun h0 => y.2 ((hzS _).mp h0)
           | exact ValuativeRel.valuation_posSubmonoid_ne_zero y)
    have keyR : ∀ a b z : R, valuation R b ≠ 0 →
        (valuation R z < valuation R a / valuation R b ↔ ¬ a ≤ᵥ z * b) := by
      intro a b z hb
      rw [← not_le, div_le_iff₀ (lt_of_le_of_ne zero_le' (Ne.symm hb)), ← map_mul, cR]
    have keyS : ∀ a b z : S, valuation S b ≠ 0 →
        (valuation S z < valuation S a / valuation S b ↔ ¬ a ≤ᵥ z * b) := by
      intro a b z hb
      rw [← not_le, div_le_iff₀ (lt_of_le_of_ne zero_le' (Ne.symm hb)), ← map_mul, cS]
    rw [hf.nhds_eq_comap x, Filter.mem_comap]
    constructor
    · rintro ⟨t, ht, hts⟩
      obtain ⟨γ, hγ⟩ := IsValuativeTopology.mem_nhds_iff.mp ht
      obtain ⟨a', b', hbS', h⟩ := surjS (γ : ValueGroupWithZero S)
      obtain ⟨a, rfl⟩ := hsurj a'
      obtain ⟨b, rfl⟩ := hsurj b'
      have hγ0 := γ.ne_zero
      rw [← h] at hγ0
      have hbS : valuation S (f b) ≠ 0 := hbS'
      have haS : valuation S (f a) ≠ 0 := fun h0 => hγ0 (by rw [h0, zero_div])
      have hbR : valuation R b ≠ 0 := by
        rw [Ne, hzR, ← hv, map_zero, ← hzS]; exact hbS
      have haR : valuation R a ≠ 0 := by
        rw [Ne, hzR, ← hv, map_zero, ← hzS]; exact haS
      refine ⟨Units.mk0 _ (div_ne_zero haR hbR), ?_⟩
      rintro _ ⟨z, hz, rfl⟩
      apply hts
      show f (x + z) ∈ t
      apply hγ
      refine ⟨f z, ?_, by simp⟩
      rw [mem_setOf_eq, ← h, keyS _ _ _ hbS, ← map_mul f, hv]
      rw [mem_setOf_eq, Units.val_mk0, keyR _ _ _ hbR] at hz
      exact hz
    · rintro ⟨γ, hγ⟩
      obtain ⟨a, b, hbR, h⟩ := surjR (γ : ValueGroupWithZero R)
      have hγ0 := γ.ne_zero
      rw [← h] at hγ0
      have haR : valuation R a ≠ 0 := fun h0 => hγ0 (by rw [h0, zero_div])
      have hbS : valuation S (f b) ≠ 0 := by
        rw [Ne, hzS, ← map_zero f, hv, ← hzR]; exact hbR
      have haS : valuation S (f a) ≠ 0 := by
        rw [Ne, hzS, ← map_zero f, hv, ← hzR]; exact haR
      refine ⟨(fun w => f x + w) '' {w | valuation S w <
        ((Units.mk0 _ (div_ne_zero haS hbS) : (ValueGroupWithZero S)ˣ) : ValueGroupWithZero S)},
        IsValuativeTopology.mem_nhds_iff.mpr ⟨Units.mk0 _ (div_ne_zero haS hbS), subset_rfl⟩, ?_⟩
      rintro y ⟨w, hw, hwy⟩
      apply hγ
      refine ⟨y - x, ?_, by simp⟩
      rw [mem_setOf_eq, ← h, keyR _ _ _ hbR]
      have hw' : f (y - x) = w := by
        rw [_root_.map_sub, ← hwy]; simp
      rw [mem_setOf_eq, Units.val_mk0, keyS _ _ _ hbS, ← hw', ← map_mul f, hv] at hw
      exact hw
