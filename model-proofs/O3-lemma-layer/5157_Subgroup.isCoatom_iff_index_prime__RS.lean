/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     Subgroup.isCoatom_iff_index_prime
Source:      Mathlib @ a02a63c2, Mathlib/GroupTheory/Nilpotent.lean, line 1246
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  O3-lemma-layer, arm RS, verified in round 1 (round 0 = first attempt)
Prover:      claude-opus-5-5
Setup:       Opus 5.5 with repair loop: arm R = repair only; arm RS = repair plus the Lean-checked lemma layer
Check:       the proof replaced the human proof in the Mathlib file above; Lean reported
             0 errors and no `sorry`; sorry/admit/native_decide/search tactics were rejected.
-/

open commutatorElement Subgroup
section WithGroup
variable {G : Type*} [Group G] (N : Subgroup G) [Normal N]
namespace Subgroup
open QuotientGroup
variable (G)
attribute [to_additive existing] upperCentralSeriesAux
variable {G}
variable (G) in
end Subgroup
namespace Group
variable (G) in
variable (G) in
variable (G) in
end Group
open Group
namespace Subgroup
variable (G)
variable {G}
attribute [to_additive existing] lowerCentralSeries
variable (S : Subgroup G)
end Subgroup
section Classical
variable (G) in
open scoped Classical in
variable [hG : IsNilpotent G]
open scoped Classical in
namespace Subgroup
open scoped Classical in
open scoped Classical in
open scoped Classical in
end Subgroup
end Classical
namespace Subgroup
end Subgroup
namespace Group
end Group
open QuotientGroup
namespace Subgroup
end Subgroup
namespace Group
end Group
namespace Subgroup
variable (G) in
end Subgroup
variable (G) in
section Prod
variable {G₁ G₂ : Type*} [Group G₁] [Group G₂]
end Prod
section BoundedPi
variable {η : Type*} {Gs : η → Type*} [∀ i, Group (Gs i)]
end BoundedPi
section FinitePi
variable {η : Type*} {Gs : η → Type*} [∀ i, Group (Gs i)]
end FinitePi
namespace Group
end Group
namespace Subgroup

@[to_additive]
theorem isCoatom_iff_index_prime [Group.IsNilpotent G] (H : Subgroup G) :
    IsCoatom H ↔ H.index.Prime := by
  constructor
  · intro hH
    have hlt : H < normalizer H := normalizerCondition_of_isNilpotent H hH.1.lt_top
    have hn : normalizer H = ⊤ := hH.2 _ hlt
    have hN : H.Normal := ⟨fun n hn' g =>
      (mem_normalizer_iff.mp (by rw [hn]; exact mem_top g) n).mp hn'⟩
    haveI := Group.isSimpleGroup_of_isCoatom hH
    have hc : center (G ⧸ H) = ⊤ := by
      rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (center (G ⧸ H)) with h | h
      · exfalso
        have := Group.IsNilpotent.inf_center_ne_bot_of_normal (G := G ⧸ H)
          (H := ⊤) top_ne_bot
        rw [top_inf_eq, h] at this
        exact this rfl
      · exact h
    letI : CommGroup (G ⧸ H) :=
      { (inferInstance : Group (G ⧸ H)) with
        mul_comm := fun a b => mem_center_iff.mp (by rw [hc]; exact mem_top b) a }
    first
    | exact IsSimpleGroup.prime_card
    | exact (CommGroup.is_simple_iff_isCyclic_and_prime_card.mp inferInstance).2
  · exact isCoatom_of_index_prime
