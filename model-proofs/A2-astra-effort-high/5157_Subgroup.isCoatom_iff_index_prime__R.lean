/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     Subgroup.isCoatom_iff_index_prime
Source:      Mathlib @ a02a63c2, Mathlib/GroupTheory/Nilpotent.lean, line 1246
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  A2-astra-effort-high, arm R, verified in round 2 (round 0 = first attempt)
Prover:      gpt-6-astra
Setup:       GPT-6 Astra, reasoning effort high (arms R, N0)
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
  refine ⟨fun h ↦ ?_, isCoatom_of_index_prime⟩
  haveI : H.Normal :=
    Group.normalizerCondition_of_isNilpotent.normal_of_coatom H h
  haveI : IsSimpleGroup (G ⧸ H) :=
    Group.isSimpleGroup_of_isCoatom h
  rw [index_eq_card, ← Group.is_simple_iff_prime_card]
  infer_instance
