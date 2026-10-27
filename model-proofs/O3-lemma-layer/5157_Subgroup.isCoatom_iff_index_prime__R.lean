/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     Subgroup.isCoatom_iff_index_prime
Source:      Mathlib @ a02a63c2, Mathlib/GroupTheory/Nilpotent.lean, line 1246
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

@[to_additive]
theorem isCoatom_iff_index_prime [Group.IsNilpotent G] (H : Subgroup G) :
    IsCoatom H ↔ H.index.Prime := by
  constructor
  · intro hH
    have hlt : H < ⊤ := lt_top_iff_ne_top.mpr hH.1
    have hnorm := hH.2 _ (normalizerCondition_of_isNilpotent H hlt)
    have hN : H.Normal := ⟨fun n hn g => by
      have : g ∈ (⊤ : Subgroup G) := mem_top g
      rw [← hnorm] at this
      exact (mem_normalizer_iff.mp this n).mp hn⟩
    have hcl : ∀ K : Subgroup (G ⧸ H), K = ⊥ ∨ K = ⊤ := by
      intro K
      have hle : H ≤ K.comap (QuotientGroup.mk' H) := by
        intro h hh
        rw [Subgroup.mem_comap, QuotientGroup.mk'_apply, (QuotientGroup.eq_one_iff h).mpr hh]
        exact one_mem K
      rcases eq_or_lt_of_le hle with h | h
      · left
        rw [eq_bot_iff]
        intro q hq
        obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective q
        have : g ∈ K.comap (QuotientGroup.mk' H) := by
          rw [Subgroup.mem_comap, QuotientGroup.mk'_apply]; exact hq
        rw [← h] at this
        rw [Subgroup.mem_bot]
        exact (QuotientGroup.eq_one_iff g).mpr this
      · right
        have htop := hH.2 _ h
        rw [eq_top_iff]
        intro q _
        obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective q
        have : g ∈ K.comap (QuotientGroup.mk' H) := by rw [htop]; exact mem_top g
        rw [Subgroup.mem_comap, QuotientGroup.mk'_apply] at this
        exact this
    obtain ⟨g, hg⟩ : ∃ g, g ∉ H := by
      by_contra hc
      push_neg at hc
      exact hH.1 (eq_top_iff.mpr fun x _ => hc x)
    obtain ⟨q, hq1⟩ : ∃ q : G ⧸ H, q ≠ 1 :=
      ⟨g, fun h => hg ((QuotientGroup.eq_one_iff g).mp h)⟩
    have hgen : ∀ x : G ⧸ H, x ≠ 1 → zpowers x = ⊤ := by
      intro x hx
      rcases hcl (zpowers x) with h | h
      · exact (hx (by rw [← Subgroup.mem_bot, ← h]; exact mem_zpowers x)).elim
      · exact h
    have hfin : IsOfFinOrder q := by
      by_cases h2 : q ^ 2 = 1
      · exact isOfFinOrder_iff_pow_eq_one.mpr ⟨2, by norm_num, h2⟩
      · have hm : q ∈ zpowers (q ^ 2) := by rw [hgen _ h2]; exact mem_top q
        obtain ⟨k, hk⟩ := mem_zpowers_iff.mp hm
        rw [isOfFinOrder_iff_zpow_eq_one]
        refine ⟨2 * k - 1, by omega, ?_⟩
        rw [zpow_sub_one, zpow_mul, show q ^ (2:ℤ) = q ^ 2 by rw [zpow_two, pow_two], hk,
          mul_inv_cancel]
    have hpos : 0 < orderOf q := hfin.orderOf_pos
    have hn1 : orderOf q ≠ 1 := fun h => hq1 (orderOf_eq_one_iff.mp h)
    have hcard : H.index = orderOf q := by
      rw [Subgroup.index, ← Nat.card_zpowers, hgen q hq1, Subgroup.card_top]
    have hdiv : ∀ m, m ∣ orderOf q → m = 1 ∨ m = orderOf q := by
      intro m hm
      by_cases h : q ^ m = 1
      · right
        exact Nat.dvd_antisymm hm (orderOf_dvd_of_pow_eq_one h)
      · left
        have hmem : q ∈ zpowers (q ^ m) := by rw [hgen _ h]; exact mem_top q
        obtain ⟨k, hk⟩ := mem_zpowers_iff.mp hmem
        have h1 : q ^ ((m : ℤ) * k - 1) = 1 := by
          rw [zpow_sub_one, zpow_mul, zpow_natCast, hk, mul_inv_cancel]
        have h2 := orderOf_dvd_iff_zpow_eq_one.mpr h1
        have h3 : (m : ℤ) ∣ (m : ℤ) * k - 1 := (Int.natCast_dvd_natCast.mpr hm).trans h2
        have h4 : (m : ℤ) ∣ 1 := by
          have := dvd_sub (dvd_mul_right (m : ℤ) k) h3
          simpa using this
        exact Nat.dvd_one.mp (by exact_mod_cast h4)
    rw [hcard]
    rcases hdiv _ (Nat.minFac_dvd (orderOf q)) with h | h
    · exact absurd h (Nat.minFac_prime hn1).one_lt.ne'
    · rw [← h]; exact Nat.minFac_prime hn1
  · intro hp
    refine ⟨fun h => ?_, fun K hK => ?_⟩
    · rw [h, Subgroup.index_top] at hp
      exact Nat.not_prime_one hp
    · rcases (Nat.dvd_prime hp).mp (Subgroup.index_dvd_of_le hK.le) with h | h
      · exact Subgroup.index_eq_one.mp h
      · exfalso
        have hmul := Subgroup.relIndex_mul_index hK.le
        rw [h] at hmul
        have : H.relIndex K = 1 :=
          Nat.eq_of_mul_eq_mul_right hp.pos (hmul.trans (one_mul _).symm)
        exact hK.ne (le_antisymm hK.le (Subgroup.relIndex_eq_one.mp this))
