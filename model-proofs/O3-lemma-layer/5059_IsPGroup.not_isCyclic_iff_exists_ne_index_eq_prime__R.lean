/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     IsPGroup.not_isCyclic_iff_exists_ne_index_eq_prime
Source:      Mathlib @ a02a63c2, Mathlib/GroupTheory/Nilpotent.lean, line 1270
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

theorem not_isCyclic_iff_exists_ne_index_eq_prime [Group.IsNilpotent G]
    [IsCoatomic (Subgroup G)] (hG : IsPGroup p G) :
    ¬ IsCyclic G ↔ ∃ H₁ H₂ : Subgroup G, H₁ ≠ H₂ ∧ H₁.index = p ∧ H₂.index = p := by
  constructor
  · intro hnc
    have hidx : ∀ M : Subgroup G, IsCoatom M → M.index = p := by
      intro M hM
      have hMtop : M < ⊤ := lt_top_iff_ne_top.mpr hM.1
      have hN := hM.2 _ (normalizerCondition_of_isNilpotent M hMtop)
      haveI hMn : M.Normal := ⟨fun n hn x => by
        have hx : x ∈ (⊤ : Subgroup G) := mem_top x
        rw [← hN] at hx
        exact (mem_normalizer_iff.mp hx n).mp hn⟩
      obtain ⟨g, -, hg⟩ := SetLike.exists_of_lt hMtop
      classical
      obtain ⟨k, hk⟩ := hG g
      have hex : ∃ k : ℕ, g ^ p ^ k ∈ M := ⟨k, by rw [hk]; exact M.one_mem⟩
      have hk0 : Nat.find hex ≠ 0 := by
        intro h0
        have := Nat.find_spec hex
        rw [h0, pow_zero, pow_one] at this
        exact hg this
      obtain ⟨h, hhM, hhp⟩ : ∃ h : G, h ∉ M ∧ h ^ p ∈ M :=
        ⟨g ^ p ^ (Nat.find hex - 1),
          Nat.find_min hex (Nat.sub_lt (Nat.pos_of_ne_zero hk0) one_pos),
          by
            rw [← pow_mul, ← pow_succ, Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr hk0)]
            exact Nat.find_spec hex⟩
      have hpow : ((h : G ⧸ M)) ^ p = 1 := by
        rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff]; exact hhp
      have hne1 : ((h : G ⧸ M)) ≠ 1 := by
        rw [Ne, QuotientGroup.eq_one_iff]; exact hhM
      have hord : orderOf (h : G ⧸ M) = p := orderOf_eq_prime hpow hne1
      have hK : (zpowers (h : G ⧸ M)).comap (QuotientGroup.mk' M) = ⊤ := by
        apply hM.2
        refine lt_of_le_of_ne ?_ ?_
        · intro m hm
          have h1 : ((m : G ⧸ M)) = 1 := by
            rw [QuotientGroup.eq_one_iff]; exact hm
          rw [mem_comap, QuotientGroup.mk'_apply, h1]
          exact one_mem _
        · intro heq
          apply hhM
          rw [heq, mem_comap, QuotientGroup.mk'_apply]
          exact mem_zpowers _
      have hall : ∀ y : G ⧸ M, y ∈ zpowers (h : G ⧸ M) := by
        intro y
        obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective y
        have : x ∈ (zpowers (h : G ⧸ M)).comap (QuotientGroup.mk' M) := by
          rw [hK]; exact mem_top x
        exact this
      show Nat.card (G ⧸ M) = p
      rw [← hord, ← Nat.card_zpowers]
      exact (Nat.card_congr (Equiv.subtypeUnivEquiv hall)).symm
    have hbot : (⊥ : Subgroup G) ≠ ⊤ := by
      intro h
      apply hnc
      exact ⟨⟨1, fun x => (show x ∈ zpowers (1 : G) by
        have : x ∈ (⊥ : Subgroup G) := by rw [h]; exact mem_top x
        rw [mem_bot] at this
        rw [this]
        exact (zpowers (1 : G)).one_mem)⟩⟩
    obtain hb | ⟨M₁, hM₁, -⟩ := IsCoatomic.eq_top_or_exists_le_coatom (⊥ : Subgroup G)
    · exact absurd hb hbot
    obtain ⟨g, -, hg⟩ := SetLike.exists_of_lt (lt_top_iff_ne_top.mpr hM₁.1)
    obtain hz | ⟨M₂, hM₂, hle⟩ := IsCoatomic.eq_top_or_exists_le_coatom (zpowers g)
    · exact (hnc ⟨⟨g, fun x => (show x ∈ zpowers g by rw [hz]; exact mem_top x)⟩⟩).elim
    · refine ⟨M₂, M₁, ?_, hidx M₂ hM₂, hidx M₁ hM₁⟩
      rintro rfl
      exact hg (hle (mem_zpowers g))
  · rintro ⟨H₁, H₂, hne, h1, h2⟩ hcyc
    obtain ⟨g, hg⟩ : ∃ g : G, ∀ x, x ∈ zpowers g := hcyc.exists_generator
    have key : ∀ H : Subgroup G, H.index = p → ∀ n : ℤ, g ^ n ∈ H ↔ (p : ℤ) ∣ n := by
      intro H hH n
      haveI : H.Normal := ⟨fun m hm x => by
        obtain ⟨a, rfl⟩ := mem_zpowers_iff.mp (hg x)
        obtain ⟨b, rfl⟩ := mem_zpowers_iff.mp (hg m)
        have : g ^ a * g ^ b * (g ^ a)⁻¹ = g ^ b := by
          rw [← zpow_neg, ← zpow_add, ← zpow_add]
          congr 1
          ring
        rw [this]
        exact hm⟩
      have hcard : Nat.card (G ⧸ H) = p := hH
      have hpow : ((g : G ⧸ H)) ^ p = 1 := by
        rw [← hcard]; exact pow_card_eq_one'
      have hne1 : ((g : G ⧸ H)) ≠ 1 := by
        intro h1
        rw [QuotientGroup.eq_one_iff] at h1
        have : H = ⊤ := by
          rw [eq_top_iff]
          intro x _
          obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp (hg x)
          exact H.zpow_mem h1 k
        rw [this, index_top] at hH
        exact hp.out.one_lt.ne hH
      have hord : orderOf (g : G ⧸ H) = p := orderOf_eq_prime hpow hne1
      rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_zpow, ← orderOf_dvd_iff_zpow_eq_one, hord]
    apply hne
    ext x
    obtain ⟨n, rfl⟩ := mem_zpowers_iff.mp (hg x)
    rw [key H₁ h1, key H₂ h2]
