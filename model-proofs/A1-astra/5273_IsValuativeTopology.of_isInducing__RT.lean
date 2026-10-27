/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     IsValuativeTopology.of_isInducing
Source:      Mathlib @ a02a63c2, Mathlib/Topology/Algebra/ValuativeRel/ValuativeTopology.lean, line 237
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  A1-astra, arm RT, verified in round 1 (round 0 = first attempt)
Prover:      gpt-6-astra
Setup:       GPT-6 Astra (Codex, effort medium): R = proof plus up to 3 repair rounds with Lean errors; RS = R plus lemma layer; RT = R with read-only Mathlib sources to search; N0-N3 = independent attempts
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
    have hvlt (a b : R) : f a <ᵥ f b ↔ a <ᵥ b := by
      simpa only [← not_vle] using not_congr (hv b a)
    have hp (a : R) : 0 <ᵥ f a ↔ 0 <ᵥ a := by
      simpa only [map_zero] using hvlt 0 a
    have ht (a b : posSubmonoid R) (z : R) :
        valuation S (f z) < valuation S (f a) / valuation S (f b) ↔
          valuation R z < valuation R a / valuation R b := by
      rw [(valuation S).lt_div_iff_mul_vlt ((hp b).2 b.property),
        (valuation R).lt_div_iff_mul_vlt b.property, ← map_mul, hvlt]
    suffices h : s ∈ 𝓝 x ↔
        ∃ γ : (ValueGroupWithZero R)ˣ,
          {z | valuation R (z - x) < γ} ⊆ s by
      simpa [Set.image_add_left, neg_add_eq_sub] using h
    rw [hf.nhds_eq_comap,
      ((IsValuativeTopology.hasBasis_nhds (f x)).comap f).mem_iff]
    simp only [true_and]
    constructor
    · rintro ⟨γ, hγ⟩
      obtain ⟨aS, bS, hab⟩ :=
        exists_valuation_posSubmonoid_div_valuation_posSubmonoid_eq γ
      obtain ⟨a, ha⟩ := hsurj (aS : S)
      obtain ⟨b, hb⟩ := hsurj (bS : S)
      let a' : posSubmonoid R :=
        ⟨a, (hp a).1 (by
          rw [ha]
          exact aS.property)⟩
      let b' : posSubmonoid R :=
        ⟨b, (hp b).1 (by
          rw [hb]
          exact bS.property)⟩
      refine ⟨Units.mk0 (valuation R a' / valuation R b')
        (div_ne_zero ((valuation R).apply_posSubmonoid_ne_zero a')
          ((valuation R).apply_posSubmonoid_ne_zero b')), ?_⟩
      intro z hz
      apply hγ
      change valuation S (f z - f x) < (γ : ValueGroupWithZero S)
      have hz' := (ht a' b' (z - x)).2 hz
      change valuation S (f (z - x)) <
        valuation S (f a) / valuation S (f b) at hz'
      simpa only [_root_.map_sub, ha, hb, hab] using hz'
    · rintro ⟨γ, hγ⟩
      obtain ⟨a, b, hab⟩ :=
        exists_valuation_posSubmonoid_div_valuation_posSubmonoid_eq γ
      let a' : posSubmonoid S := ⟨f a, (hp a).2 a.property⟩
      let b' : posSubmonoid S := ⟨f b, (hp b).2 b.property⟩
      refine ⟨Units.mk0 (valuation S a' / valuation S b')
        (div_ne_zero ((valuation S).apply_posSubmonoid_ne_zero a')
          ((valuation S).apply_posSubmonoid_ne_zero b')), ?_⟩
      intro z hz
      apply hγ
      change valuation R (z - x) < (γ : ValueGroupWithZero R)
      rw [← hab]
      apply (ht a b (z - x)).1
      change valuation S (f z - f x) <
        valuation S (f a) / valuation S (f b) at hz
      simpa only [_root_.map_sub] using hz
