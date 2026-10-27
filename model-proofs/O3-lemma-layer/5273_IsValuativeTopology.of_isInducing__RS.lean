/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     IsValuativeTopology.of_isInducing
Source:      Mathlib @ a02a63c2, Mathlib/Topology/Algebra/ValuativeRel/ValuativeTopology.lean, line 237
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  O3-lemma-layer, arm RS, verified in round 2 (round 0 = first attempt)
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
    have hR : ∀ x y : R, x ≤ᵥ y ↔ valuation R x ≤ valuation R y := fun x y => by
      first
      | exact Valuation.Compatible.rel_iff_le x y
      | exact Valuation.Compatible.vle_iff_le x y
      | exact (ValuativeRel.valuation_le_valuation).symm
      | simp
    have hS : ∀ x y : S, x ≤ᵥ y ↔ valuation S x ≤ valuation S y := fun x y => by
      first
      | exact Valuation.Compatible.rel_iff_le x y
      | exact Valuation.Compatible.vle_iff_le x y
      | exact (ValuativeRel.valuation_le_valuation).symm
      | simp
    have key : ∀ a b z : R, ¬ b ≤ᵥ 0 →
        (valuation R z < valuation R a / valuation R b ↔
          valuation S (f z) < valuation S (f a) / valuation S (f b)) := by
      intro a b z hb
      have hb1 : valuation R b ≠ 0 := fun h => hb ((hR b 0).2 (by rw [h, map_zero]))
      have hb2 : valuation S (f b) ≠ 0 := fun h => hb ((hv b 0).1
        (by rw [map_zero]; exact (hS _ _).2 (by rw [h, map_zero])))
      rw [← not_le, ← not_le, div_le_iff₀ (zero_lt_iff.2 hb1), div_le_iff₀ (zero_lt_iff.2 hb2),
        ← Valuation.map_mul, ← Valuation.map_mul, ← map_mul f, ← hR, ← hS, hv]
    rw [hf.nhds_eq_comap, mem_comap]
    constructor
    · rintro ⟨t, ht, hts⟩
      obtain ⟨γ', hγ'⟩ := (IsValuativeTopology.mem_nhds_iff).1 ht
      obtain ⟨a', b', hab⟩ : ∃ (a : S) (b : posSubmonoid S),
          valuation S a / valuation S (b : S) = (γ' : ValueGroupWithZero S) := by
        first
        | exact ValuativeRel.exists_valuation_div_valuation_eq _
        | exact ValueGroupWithZero.ind (motive := fun t => ∃ (a : S) (b : posSubmonoid S),
            valuation S a / valuation S (b : S) = t)
            (fun x y => ⟨x, y, (ValueGroupWithZero.mk_eq_div x y).symm⟩) _
        | (generalize (γ' : ValueGroupWithZero S) = t
           induction t using ValueGroupWithZero.ind with
           | mk x y => exact ⟨x, y, (ValueGroupWithZero.mk_eq_div x y).symm⟩)
      obtain ⟨a, rfl⟩ := hsurj a'
      obtain ⟨b, hb⟩ := hsurj (b' : S)
      have hne : valuation S (f a) / valuation S (b' : S) ≠ 0 := by
        rw [hab]; exact γ'.ne_zero
      have hb'0 : valuation S (b' : S) ≠ 0 := fun h => hne (by rw [h, div_zero])
      have ha'0 : valuation S (f a) ≠ 0 := fun h => hne (by rw [h, zero_div])
      rw [← hb] at hab hb'0
      have hb0 : ¬ b ≤ᵥ 0 := fun h => hb'0 (by
        have := (hv b 0).2 h
        rw [map_zero, hS] at this
        simpa using this)
      have ha0 : valuation R a ≠ 0 := fun h => ha'0 (by
        have h1 : a ≤ᵥ 0 := (hR a 0).2 (by rw [h, map_zero])
        have := (hv a 0).2 h1
        rw [map_zero, hS] at this
        simpa using this)
      have hb1 : valuation R b ≠ 0 := fun h => hb0 ((hR b 0).2 (by rw [h, map_zero]))
      refine ⟨Units.mk0 _ (div_ne_zero ha0 hb1), ?_⟩
      rintro _ ⟨z, hz, rfl⟩
      apply hts
      show f (x + z) ∈ t
      apply hγ'
      refine ⟨f z, ?_, (map_add f x z).symm⟩
      show valuation S (f z) < (γ' : ValueGroupWithZero S)
      rw [← hab]
      exact (key a b z hb0).1 hz
    · rintro ⟨γ, hγ⟩
      obtain ⟨a, b', hab⟩ : ∃ (a : R) (b : posSubmonoid R),
          valuation R a / valuation R (b : R) = (γ : ValueGroupWithZero R) := by
        first
        | exact ValuativeRel.exists_valuation_div_valuation_eq _
        | exact ValueGroupWithZero.ind (motive := fun t => ∃ (a : R) (b : posSubmonoid R),
            valuation R a / valuation R (b : R) = t)
            (fun x y => ⟨x, y, (ValueGroupWithZero.mk_eq_div x y).symm⟩) _
        | (generalize (γ : ValueGroupWithZero R) = t
           induction t using ValueGroupWithZero.ind with
           | mk x y => exact ⟨x, y, (ValueGroupWithZero.mk_eq_div x y).symm⟩)
      have hne : valuation R a / valuation R (b' : R) ≠ 0 := by
        rw [hab]; exact γ.ne_zero
      have hb1 : valuation R (b' : R) ≠ 0 := fun h => hne (by rw [h, div_zero])
      have ha1 : valuation R a ≠ 0 := fun h => hne (by rw [h, zero_div])
      have hb0 : ¬ (b' : R) ≤ᵥ 0 := fun h => hb1 (by
        have := (hR _ _).1 h
        simpa using this)
      have ha0 : ¬ a ≤ᵥ 0 := fun h => ha1 (by
        have := (hR _ _).1 h
        simpa using this)
      have hfb : valuation S (f (b' : R)) ≠ 0 := fun h => hb0 ((hv _ 0).1
        (by rw [map_zero]; exact (hS _ _).2 (by rw [h, map_zero])))
      have hfa : valuation S (f a) ≠ 0 := fun h => ha0 ((hv _ 0).1
        (by rw [map_zero]; exact (hS _ _).2 (by rw [h, map_zero])))
      refine ⟨(f x + ·) '' {w | valuation S w < (Units.mk0 _ (div_ne_zero hfa hfb) :
        ValueGroupWithZero S)}, (IsValuativeTopology.mem_nhds_iff).2 ⟨_, subset_rfl⟩, ?_⟩
      intro y hy
      obtain ⟨w, hw, hwy⟩ := hy
      have hwy' : f x + w = f y := hwy
      have hw' : f (y - x) = w := by
        rw [_root_.map_sub f, ← hwy']; abel
      apply hγ
      refine ⟨y - x, ?_, by abel⟩
      show valuation R (y - x) < (γ : ValueGroupWithZero R)
      rw [← hab]
      rw [key a (b' : R) (y - x) hb0, hw']
      exact hw
