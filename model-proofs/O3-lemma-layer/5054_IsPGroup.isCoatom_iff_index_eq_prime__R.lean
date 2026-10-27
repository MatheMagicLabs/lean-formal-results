/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     IsPGroup.isCoatom_iff_index_eq_prime
Source:      Mathlib @ a02a63c2, Mathlib/GroupTheory/Nilpotent.lean, line 1261
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  O3-lemma-layer, arm R, verified in round 1 (round 0 = first attempt)
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
  constructor
  · intro hH
    haveI : H.Normal := normalizerCondition_of_isNilpotent.normal_of_coatom H hH
    have hQ : IsPGroup p (G ⧸ H) := hG.to_quotient H
    obtain ⟨g, hg⟩ : ∃ g : G, g ∉ H := by
      by_contra h
      push_neg at h
      exact hH.1 (eq_top_iff.mpr fun x _ => h x)
    obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.mp hQ) (QuotientGroup.mk' H g)
    have hk0 : k ≠ 0 := by
      rintro rfl
      rw [pow_zero, orderOf_eq_one_iff, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hk
      exact hg hk
    obtain ⟨h, hh⟩ : ∃ h, h = g ^ (p ^ (k - 1)) := ⟨_, rfl⟩
    have hord : orderOf (QuotientGroup.mk' H h) = p := by
      have := orderOf_eq_prime_pow (p := p) (n := 0) (x := QuotientGroup.mk' H h) ?_ ?_
      · simpa using this
      · rw [pow_zero, pow_one, hh, map_pow]
        exact pow_ne_one_of_lt_orderOf (pow_pos hp.out.pos _).ne'
          (by rw [hk]; exact Nat.pow_lt_pow_right hp.out.one_lt (by omega))
      · rw [zero_add, pow_one, hh, map_pow, ← pow_mul, ← pow_succ,
          Nat.sub_add_cancel (by omega), ← hk]
        exact pow_orderOf_eq_one _
    have hh' : h ∉ H := by
      intro hm
      have : QuotientGroup.mk' H h = 1 := by
        rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]; exact hm
      rw [this, orderOf_one] at hord
      exact hp.out.one_lt.ne hord
    have hsup : H ⊔ zpowers h = ⊤ :=
      hH.2 _ (lt_of_le_of_ne le_sup_left
        (fun he => hh' (by rw [he]; exact mem_sup_right (mem_zpowers h))))
    have htop : zpowers (QuotientGroup.mk' H h) = ⊤ := by
      have := congrArg (Subgroup.map (QuotientGroup.mk' H)) hsup
      rw [Subgroup.map_sup,
        (Subgroup.map_eq_bot_iff _).mpr (by rw [QuotientGroup.ker_mk']),
        bot_sup_eq, MonoidHom.map_zpowers, ← MonoidHom.range_eq_map,
        MonoidHom.range_eq_top.mpr (QuotientGroup.mk'_surjective H)] at this
      exact this
    show Nat.card (G ⧸ H) = p
    rw [← Subgroup.card_top (G := G ⧸ H), ← htop, Nat.card_zpowers, hord]
  · intro hH
    refine ⟨fun h => ?_, fun K hK => ?_⟩
    · rw [h, index_top] at hH
      exact hp.out.one_lt.ne hH
    · have := relIndex_mul_index hK.le
      rw [hH] at this
      rcases hp.out.eq_one_or_self_of_dvd _ (Dvd.intro _ this) with h1 | h1
      · exact (hK.ne (le_antisymm hK.le (relIndex_eq_one.mp h1))).elim
      · rw [h1] at this
        exact index_eq_one.mp (Nat.eq_of_mul_eq_mul_left hp.out.pos (by rw [mul_one]; exact this))
