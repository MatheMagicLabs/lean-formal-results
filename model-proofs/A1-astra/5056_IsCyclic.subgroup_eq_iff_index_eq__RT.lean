/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     IsCyclic.subgroup_eq_iff_index_eq
Source:      Mathlib @ a02a63c2, Mathlib/GroupTheory/SpecificGroups/Cyclic.lean, line 985
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  A1-astra, arm RT, verified in round 0 (round 0 = first attempt)
Prover:      gpt-6-astra
Setup:       GPT-6 Astra (Codex, effort medium): R = proof plus up to 3 repair rounds with Lean errors; RS = R plus lemma layer; RT = R with read-only Mathlib sources to search; N0-N3 = independent attempts
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
  rw [le_antisymm_iff, IsCyclic.subgroup_le_iff_index_dvd,
    IsCyclic.subgroup_le_iff_index_dvd]
  exact ⟨fun ⟨h₁, h₂⟩ => Nat.dvd_antisymm h₂ h₁,
    fun h => ⟨h.symm.dvd, h.dvd⟩⟩
