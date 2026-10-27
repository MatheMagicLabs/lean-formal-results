/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     IsValuativeTopology.of_isInducing
Source:      Mathlib @ a02a63c2, Mathlib/Topology/Algebra/ValuativeRel/ValuativeTopology.lean, line 237
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  A1-astra, arm R, verified in round 2 (round 0 = first attempt)
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
    set_option maxHeartbeats 0 in
      classical
      have hlt (a b : R) : f a <ᵥ f b ↔ a <ᵥ b :=
        not_congr (hv b a)
      have hballs :
          (∀ (y : R) (t : Set R),
            (∃ γ : (ValueGroupWithZero R)ˣ,
              (fun z ↦ y + z) '' {z | valuation R z < ↑γ} ⊆ t) ↔
            ∃ a b : posSubmonoid R,
              ∀ z, z * b.1 <ᵥ a.1 → y + z ∈ t) ∧
          (∀ (y : S) (t : Set S),
            (∃ γ : (ValueGroupWithZero S)ˣ,
              (fun z ↦ y + z) '' {z | valuation S z < ↑γ} ⊆ t) ↔
            ∃ a b : posSubmonoid S,
              ∀ z, z * b.1 <ᵥ a.1 → y + z ∈ t) := by
        constructor <;> intro y t
        all_goals
          constructor
          · rintro ⟨γ, hγ⟩
            obtain ⟨a, b, hab⟩ :=
              exists_valuation_posSubmonoid_div_valuation_posSubmonoid_eq γ
            refine ⟨a, b, ?_⟩
            intro z hz
            apply hγ
            refine ⟨z, ?_, rfl⟩
            change (valuation _) z < ↑γ
            rw [← hab,
              lt_div_iff₀ (pos_iff_ne_zero.mpr (valuation_posSubmonoid_ne_zero b)),
              ← _root_.map_mul]
            exact (Valuation.vlt_iff_lt (valuation _)).mp hz
          · rintro ⟨a, b, h⟩
            refine ⟨Units.mk0 ((valuation _) a.1 / (valuation _) b.1)
              (div_ne_zero (valuation_posSubmonoid_ne_zero a)
                (valuation_posSubmonoid_ne_zero b)), ?_⟩
            rintro w ⟨z, hz, rfl⟩
            apply h z
            change (valuation _) z < (valuation _) a.1 / (valuation _) b.1 at hz
            rw [lt_div_iff₀
              (pos_iff_ne_zero.mpr (valuation_posSubmonoid_ne_zero b)),
              ← _root_.map_mul] at hz
            exact (Valuation.vlt_iff_lt (valuation _)).mpr hz
      rw [hf.nhds_eq_comap, Filter.mem_comap, hballs.1 x s]
      constructor
      · rintro ⟨t, ht, hts⟩
        obtain ⟨a, b, hab⟩ :=
          (hballs.2 (f x) t).mp (IsValuativeTopology.mem_nhds_iff.mp ht)
        obtain ⟨a', ha'⟩ := hsurj a.1
        obtain ⟨b', hb'⟩ := hsurj b.1
        have ha0 : 0 <ᵥ a' := by
          apply (hlt 0 a').mp
          simpa only [_root_.map_zero, ha'] using zero_vlt_coe_posSubmonoid a
        have hb0 : 0 <ᵥ b' := by
          apply (hlt 0 b').mp
          simpa only [_root_.map_zero, hb'] using zero_vlt_coe_posSubmonoid b
        refine ⟨⟨a', ha0⟩, ⟨b', hb0⟩, ?_⟩
        intro z hz
        apply hts
        change f (x + z) ∈ t
        rw [_root_.map_add]
        apply hab (f z)
        simpa only [_root_.map_mul, ha', hb'] using
          (hlt (z * b') a').mpr hz
      · rintro ⟨a, b, hab⟩
        refine ⟨{w : S | (w - f x) * f b.1 <ᵥ f a.1}, ?_, ?_⟩
        · apply IsValuativeTopology.mem_nhds_iff.mpr
          apply (hballs.2 (f x) _).mpr
          have ha0 : 0 <ᵥ f a.1 := by
            simpa only [_root_.map_zero] using
              (hlt 0 a.1).mpr (zero_vlt_coe_posSubmonoid a)
          have hb0 : 0 <ᵥ f b.1 := by
            simpa only [_root_.map_zero] using
              (hlt 0 b.1).mpr (zero_vlt_coe_posSubmonoid b)
          refine ⟨⟨f a.1, ha0⟩, ⟨f b.1, hb0⟩, ?_⟩
          intro z hz
          change (f x + z - f x) * f b.1 <ᵥ f a.1
          have he : f x + z - f x = z := by abel
          rw [he]
          exact hz
        · intro y hy
          change (f y - f x) * f b.1 <ᵥ f a.1 at hy
          have h : (y - x) * b.1 <ᵥ a.1 := by
            apply (hlt ((y - x) * b.1) a.1).mp
            simpa only [_root_.map_mul, _root_.map_sub] using hy
          have he : x + (y - x) = y := by abel
          exact he ▸ hab (y - x) h
