/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     IsPGroup.isCoatom_iff_index_eq_prime
Source:      Mathlib @ a02a63c2, Mathlib/GroupTheory/Nilpotent.lean, line 1261
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  O3LA3-leanstral-agent-feedback, arm rueck, verified in final
Prover:      labs-leanstral-1-5
Setup:       Leanstral 1.5 agent with goal-state feedback (arm rueck)
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
  constructor
  · intro h
    have hprime : H.index.Prime := (isCoatom_iff_index_prime H).mp h
    have hfin : H.FiniteIndex := ⟨hprime.ne_zero⟩
    obtain ⟨n, hn⟩ := hG.index H
    have hp_prime : Nat.Prime p := Fact.out
    have hprime_pow : Nat.Prime (p ^ n) := by rwa [← hn]
    have hn0 : n ≠ 0 := by
      intro hzero
      rw [hzero, pow_zero] at hprime_pow
      exact Nat.not_prime_one hprime_pow
    have h_dvd : p ∣ (p ^ n) ^ 1 := by
      rw [pow_one]
      exact dvd_pow (dvd_refl p) hn0
    have h_eq : p = p ^ n :=
      Nat.prime_eq_prime_of_dvd_pow hp_prime hprime_pow h_dvd
    have hn1 : n = 1 := by
      have h_eq' : p ^ n = p ^ 1 := by
        rw [pow_one]
        exact h_eq.symm
      exact (Nat.pow_right_injective (Nat.succ_le_of_lt hp_prime.one_lt)) h_eq'
    rw [hn1, pow_one] at hn
    exact hn
  · intro h
    have hprime : H.index.Prime := by
      rw [h]
      exact Fact.out
    exact isCoatom_of_index_prime hprime
