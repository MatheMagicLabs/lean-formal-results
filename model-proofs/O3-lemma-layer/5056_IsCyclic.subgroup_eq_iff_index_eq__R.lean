/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     IsCyclic.subgroup_eq_iff_index_eq
Source:      Mathlib @ a02a63c2, Mathlib/GroupTheory/SpecificGroups/Cyclic.lean, line 985
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  O3-lemma-layer, arm R, verified in round 2 (round 0 = first attempt)
Prover:      claude-opus-5-5
Setup:       Opus 5.5 with repair loop: arm R = repair only; arm RS = repair plus the Lean-checked lemma layer
Check:       the proof replaced the human proof in the Mathlib file above; Lean reported
             0 errors and no `sorry`; sorry/admit/native_decide/search tactics were rejected.
-/

variable {α G G' : Type*} {a : α}
section Cyclic
open Subgroup
variable [Group α] [Group G] [Group G']
open Finset Nat
section Totient
variable [DecidableEq α] [Fintype α] (hn : ∀ n : ℕ, 0 < n → #{a : α | a ^ n = 1} ≤ n)
open Nat
end Totient
end Cyclic
section QuotientCenter
open Subgroup
variable [Group G] [Group G']
variable (G) in
end QuotientCenter
namespace IsSimpleGroup
section CommSimpleGroup
variable [CommGroup α] [IsSimpleGroup α]
end CommSimpleGroup
end IsSimpleGroup
open scoped IsMulCommutative in
open Subgroup in
section SpecificInstances
end SpecificInstances
section EquivInt
end EquivInt
section Exponent
open Monoid
end Exponent
section ZMod
open Subgroup AddSubgroup
section addGenerator
variable [AddGroup G] {g : G} (hg : ∀ x, x ∈ zmultiples g) {n : ℕ} (hn : Nat.card G = n)
end addGenerator
section mulGenerator
variable [Group G] {g : G} (hg : ∀ x, x ∈ zpowers g) {n : ℕ} (hn : Nat.card G = n)
end mulGenerator
section Infinite
variable [Infinite G]
end Infinite
set_option backward.isDefEq.respectTransparency.types false in
variable (G) in
variable (G) in
end ZMod
section powMonoidHom
variable (G)
end powMonoidHom
section generator
open Subgroup
variable [Group G] [Group G'] {g : G} (hg : ∀ x, x ∈ zpowers g) {g' : G'}
section monoidHom
variable (hg' : orderOf g' ∣ orderOf (g : G))
end monoidHom
section mulEquiv
variable (hg' : ∀ x, x ∈ zpowers g') (h : orderOf g = orderOf g')
end mulEquiv
end generator
section prod
section
variable (M N : Type*) [Group M] [Group N] [cyc : IsCyclic (M × N)]
end
end prod
section WithZero
end WithZero
section SubgroupCard
variable [Group G] [IsCyclic G] {H K : Subgroup G}

@[to_additive /-- In an additive cyclic group, `H = K` iff `H.index = K.index`. -/]
theorem IsCyclic.subgroup_eq_iff_index_eq :
    H = K ↔ H.index = K.index := by
  constructor
  · rintro rfl; rfl
  · intro h
    obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := G)
    have hcomm : ∀ x y : G, x * y = y * x := by
      intro x y
      obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp (hg x)
      obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp (hg y)
      rw [← zpow_add, ← zpow_add, add_comm]
    have key : ∀ L : Subgroup G, ∀ k : ℤ, g ^ k ∈ L ↔ (L.index : ℤ) ∣ k := by
      intro L k
      haveI hN : L.Normal :=
        ⟨fun n hn x => by rw [hcomm x n, mul_inv_cancel_right]; exact hn⟩
      have hgen : ∀ y : G ⧸ L, y ∈ Subgroup.zpowers (g : G ⧸ L) := by
        intro y
        obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective y
        obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp (hg x)
        exact Subgroup.mem_zpowers_iff.mpr ⟨k, (QuotientGroup.mk_zpow L g k).symm⟩
      have ho : orderOf (g : G ⧸ L) = L.index := by
        rw [orderOf_eq_card_of_forall_mem_zpowers hgen]
        rfl
      rw [← ho, orderOf_dvd_iff_zpow_eq_one, ← QuotientGroup.mk_zpow,
        QuotientGroup.eq_one_iff]
    ext x
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp (hg x)
    rw [key H, key K, h]
