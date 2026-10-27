/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     IsPGroup.not_isCyclic_iff_exists_ne_index_eq_prime
Source:      Mathlib @ a02a63c2, Mathlib/GroupTheory/Nilpotent.lean, line 1270
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  LS1-leanstral-loop, arm L3, verified in round 1 (round 0 = first attempt)
Prover:      labs-leanstral-1-5
Setup:       Leanstral 1.5 in a fixed check-and-repair loop: L1 = 1 candidate per round, L3 = up to 3
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
  · intro h_not_cyclic
    have h_exists_coatoms : ∃ (M₁ M₂ : Subgroup G), IsCoatom M₁ ∧ IsCoatom M₂ ∧ M₁ ≠ M₂ := by
      by_contra h_all_eq
      push_neg at h_all_eq
      have h_cyclic : IsCyclic G := isCyclic_of_isCoatom_subsingleton h_all_eq
      exact h_not_cyclic h_cyclic
    rcases h_exists_coatoms with ⟨M₁, M₂, hM₁, hM₂, hne⟩
    have hi₁ : M₁.index = p := ((IsPGroup.isCoatom_iff_index_eq_prime hG).mp hM₁)
    have hi₂ : M₂.index = p := ((IsPGroup.isCoatom_iff_index_eq_prime hG).mp hM₂)
    exact ⟨M₁, M₂, hne, hi₁, hi₂⟩
  · intro h
    rcases h with ⟨H₁, H₂, hne, hi₁, hi₂⟩
    intro h_cyclic
    haveI := h_cyclic
    have h_eq : H₁ = H₂ := (IsCyclic.subgroup_eq_iff_index_eq.mpr (hi₁.trans hi₂.symm))
    exact hne h_eq
