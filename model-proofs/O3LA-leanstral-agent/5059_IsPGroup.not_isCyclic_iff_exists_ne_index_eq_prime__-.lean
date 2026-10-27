/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     IsPGroup.not_isCyclic_iff_exists_ne_index_eq_prime
Source:      Mathlib @ a02a63c2, Mathlib/GroupTheory/Nilpotent.lean, line 1270
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  O3LA-leanstral-agent, arm -, verified in final
Prover:      labs-leanstral-1-5
Setup:       Leanstral 1.5 as a tool-using agent (Mistral Vibe)
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
end Subgroup
namespace IsPGroup
variable {p : ℕ} [hp : Fact p.Prime]

theorem not_isCyclic_iff_exists_ne_index_eq_prime [Group.IsNilpotent G]
    [IsCoatomic (Subgroup G)] (hG : IsPGroup p G) :
    ¬ IsCyclic G ↔ ∃ H₁ H₂ : Subgroup G, H₁ ≠ H₂ ∧ H₁.index = p ∧ H₂.index = p := by
  constructor
  · intro hnc
    have h_exists : ∃ M₁ M₂ : Subgroup G, IsCoatom M₁ ∧ IsCoatom M₂ ∧ M₁ ≠ M₂ := by
      by_contra! h_all_eq
      have hcyc : IsCyclic G := isCyclic_of_isCoatom_subsingleton h_all_eq
      exact hnc hcyc
    rcases h_exists with ⟨M₁, M₂, hM₁, hM₂, hne⟩
    have hM₁_idx : M₁.index = p := (hG.isCoatom_iff_index_eq_prime).mp hM₁
    have hM₂_idx : M₂.index = p := (hG.isCoatom_iff_index_eq_prime).mp hM₂
    exact ⟨M₁, M₂, hne, hM₁_idx, hM₂_idx⟩
  · intro ⟨H₁, H₂, hne, hH₁, hH₂⟩
    intro hcyc
    apply hne
    haveI : IsCyclic G := hcyc
    exact (IsCyclic.subgroup_eq_iff_index_eq (H := H₁) (K := H₂)).mpr (hH₁.trans hH₂.symm)
