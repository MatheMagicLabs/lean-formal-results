/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     IsPGroup.isCoatom_iff_index_eq_prime
Source:      Mathlib @ a02a63c2, Mathlib/GroupTheory/Nilpotent.lean, line 1261
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  O4-layer-with-search, arm RT, verified in round 0 (round 0 = first attempt)
Prover:      claude-opus-5-5
Setup:       Opus 5.5 with repair loop, lemma layer and name search (arm RT)
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

theorem isCoatom_iff_index_eq_prime [Group.IsNilpotent G] (hG : IsPGroup p G) {H : Subgroup G} :
    IsCoatom H ↔ H.index = p := by
  rw [Subgroup.isCoatom_iff_index_prime]
  constructor
  · intro h
    haveI : H.FiniteIndex := Subgroup.finiteIndex_iff.mpr h.ne_zero
    obtain ⟨n, hn⟩ := hG.index H
    rw [hn] at h ⊢
    have hn0 : n ≠ 0 := by
      rintro rfl
      simp at h
      exact Nat.not_prime_one h
    have hdvd : p ∣ p ^ n := dvd_pow_self p hn0
    rcases h.eq_one_or_self_of_dvd p hdvd with h1 | h1
    · exact absurd h1 hp.out.one_lt.ne'
    · exact h1.symm
  · intro h
    rw [h]
    exact hp.out
