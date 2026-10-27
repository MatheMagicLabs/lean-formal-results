/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     Subgroup.isCoatom_iff_index_prime
Source:      Mathlib @ a02a63c2, Mathlib/GroupTheory/Nilpotent.lean, line 1246
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  A1-astra, arm RS, verified in round 1 (round 0 = first attempt)
Prover:      gpt-6-astra
Setup:       GPT-6 Astra (Codex, effort medium): R = proof plus up to 3 repair rounds with Lean errors; RS = R plus lemma layer; RT = R with read-only Mathlib sources to search; N0-N3 = independent attempts
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
    haveI : H.Normal := by
      first
      | exact hH.normal
      | apply normalizer_eq_top_iff.mp
        apply hH.2
        first
        | exact Group.normalizerCondition_of_isNilpotent H hH.ne_top
        | exact Group.normalizerCondition_of_isNilpotent H hH.lt_top
        | exact Group.IsNilpotent.normalizerCondition H hH.ne_top
        | exact Group.IsNilpotent.normalizerCondition H hH.lt_top
    haveI : IsSimpleGroup (G ⧸ H) :=
      Group.isSimpleGroup_of_isCoatom hH
    change (Nat.card (G ⧸ H)).Prime
    exact IsSimpleGroup.prime_card
  · exact H.isCoatom_of_index_prime
