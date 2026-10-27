/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     IsPGroup.not_isCyclic_iff_exists_ne_index_eq_prime
Source:      Mathlib @ a02a63c2, Mathlib/GroupTheory/Nilpotent.lean, line 1270
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

theorem not_isCyclic_iff_exists_ne_index_eq_prime [Group.IsNilpotent G]
    [IsCoatomic (Subgroup G)] (hG : IsPGroup p G) :
    ¬ IsCyclic G ↔ ∃ H₁ H₂ : Subgroup G, H₁ ≠ H₂ ∧ H₁.index = p ∧ H₂.index = p := by
  constructor
  · intro h
    by_contra hne
    push_neg at hne
    apply h
    apply isCyclic_of_isCoatom_subsingleton
    intro M₁ M₂ h1 h2
    rw [hG.isCoatom_iff_index_eq_prime] at h1 h2
    by_contra hM
    exact hne M₁ M₂ hM h1 h2
  · rintro ⟨H₁, H₂, hne, h1, h2⟩ hcyc
    obtain ⟨g, hg⟩ := hcyc.exists_generator
    have hcomm : ∀ a b : G, a * b = b * a := by
      intro a b
      obtain ⟨i, rfl⟩ := mem_zpowers_iff.mp (hg a)
      obtain ⟨j, rfl⟩ := mem_zpowers_iff.mp (hg b)
      rw [← zpow_add, ← zpow_add, add_comm]
    have key : ∀ H : Subgroup G, H.index = p → H = zpowers (g ^ p) := by
      intro H hH
      haveI hN : H.Normal := ⟨fun n hn a => by rw [hcomm a n, mul_inv_cancel_right]; exact hn⟩
      have hpm : g ^ p ∈ H := by
        have := H.pow_index_mem g
        rw [hH] at this
        exact this
      have hpz : g ^ (p : ℤ) ∈ H := by rw [zpow_natCast]; exact hpm
      apply le_antisymm
      · intro x hx
        obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp (hg x)
        have hd : g ^ ((Int.gcd k p : ℕ) : ℤ) ∈ H := by
          rw [Int.gcd_eq_gcd_ab, zpow_add, zpow_mul, zpow_mul]
          exact H.mul_mem (H.zpow_mem hx _) (H.zpow_mem hpz _)
        rcases hp.out.eq_one_or_self_of_dvd _
            (Int.natCast_dvd_natCast.mp (Int.gcd_dvd_right (a := k) (b := (p : ℤ))))
          with hd1 | hdp
        · exfalso
          rw [hd1, Nat.cast_one, zpow_one] at hd
          have htop : H = ⊤ := eq_top_iff.mpr fun y _ => by
            obtain ⟨j, rfl⟩ := mem_zpowers_iff.mp (hg y)
            exact H.zpow_mem hd j
          rw [htop, index_top] at hH
          exact hp.out.one_lt.ne hH
        · have hdk : (p : ℤ) ∣ k := by
            have := Int.gcd_dvd_left (a := k) (b := (p : ℤ))
            rwa [hdp] at this
          obtain ⟨m, rfl⟩ := hdk
          exact mem_zpowers_iff.mpr ⟨m, by rw [← zpow_natCast, ← zpow_mul]⟩
      · rw [zpowers_le]
        exact hpm
    exact hne ((key H₁ h1).trans (key H₂ h2).symm)
