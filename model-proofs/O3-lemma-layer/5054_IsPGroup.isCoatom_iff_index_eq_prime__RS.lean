/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     IsPGroup.isCoatom_iff_index_eq_prime
Source:      Mathlib @ a02a63c2, Mathlib/GroupTheory/Nilpotent.lean, line 1261
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
end Subgroup
namespace IsPGroup
variable {p : ℕ} [hp : Fact p.Prime]

theorem isCoatom_iff_index_eq_prime [Group.IsNilpotent G] (hG : IsPGroup p G) {H : Subgroup G} :
    IsCoatom H ↔ H.index = p := by
  rw [Subgroup.isCoatom_iff_index_prime]
  constructor
  · intro h
    haveI : H.FiniteIndex := ⟨h.ne_zero⟩
    obtain ⟨n, hn⟩ := hG.index H
    rw [hn] at h ⊢
    have hn0 : n ≠ 0 := by
      rintro rfl
      rw [pow_zero] at h
      exact Nat.not_prime_one h
    exact ((Nat.prime_dvd_prime_iff_eq hp.out h).mp (dvd_pow_self p hn0)).symm
  · intro h
    rw [h]
    exact hp.out
