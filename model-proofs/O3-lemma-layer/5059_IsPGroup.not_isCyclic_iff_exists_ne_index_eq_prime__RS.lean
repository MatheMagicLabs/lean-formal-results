/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     IsPGroup.not_isCyclic_iff_exists_ne_index_eq_prime
Source:      Mathlib @ a02a63c2, Mathlib/GroupTheory/Nilpotent.lean, line 1270
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  O3-lemma-layer, arm RS, verified in round 0 (round 0 = first attempt)
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
end Subgroup
namespace IsPGroup
variable {p : ℕ} [hp : Fact p.Prime]

theorem not_isCyclic_iff_exists_ne_index_eq_prime [Group.IsNilpotent G]
    [IsCoatomic (Subgroup G)] (hG : IsPGroup p G) :
    ¬ IsCyclic G ↔ ∃ H₁ H₂ : Subgroup G, H₁ ≠ H₂ ∧ H₁.index = p ∧ H₂.index = p := by
  constructor
  · intro h
    by_contra hc
    apply h
    apply isCyclic_of_isCoatom_subsingleton
    intro M₁ M₂ h1 h2
    rw [hG.isCoatom_iff_index_eq_prime] at h1 h2
    by_contra hne
    exact hc ⟨M₁, M₂, hne, h1, h2⟩
  · rintro ⟨H₁, H₂, hne, h1, h2⟩ hcyc
    apply hne
    rw [IsCyclic.subgroup_eq_iff_index_eq]
    rw [h1, h2]
