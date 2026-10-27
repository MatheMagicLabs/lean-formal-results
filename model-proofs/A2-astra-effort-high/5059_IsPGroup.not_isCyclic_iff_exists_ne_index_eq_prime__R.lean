/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     IsPGroup.not_isCyclic_iff_exists_ne_index_eq_prime
Source:      Mathlib @ a02a63c2, Mathlib/GroupTheory/Nilpotent.lean, line 1270
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  A2-astra-effort-high, arm R, verified in round 3 (round 0 = first attempt)
Prover:      gpt-6-astra
Setup:       GPT-6 Astra, reasoning effort high (arms R, N0)
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
  classical
  have hindex {H : Subgroup G} (hH : IsCoatom H) : H.index = p := by
    first
    | exact (hG.isCoatom_iff_index_eq_prime).mp hH
    | exact (hG.isCoatom_iff_index_eq_prime H).mp hH
    | exact hG.index_eq_prime_of_isCoatom hH
    | exact hG.index_eq_prime_of_isCoatom H hH
  have hex (H : Subgroup G) (hH : H ≠ ⊤) :
      ∃ K : Subgroup G, IsCoatom K ∧ H ≤ K := by
    rcases (inferInstance : IsCoatomic (Subgroup G)) with ⟨h⟩
    first
    | obtain ⟨K, ha, hb⟩ := h H hH
      exact ⟨K, by assumption, by assumption⟩
    | rcases h H with ht | ⟨K, ha, hb⟩
      · exact (hH ht).elim
      · exact ⟨K, by assumption, by assumption⟩
  constructor
  · intro hn
    have hz (x : G) : zpowers x ≠ ⊤ := by
      intro hx
      exact hn (isCyclic_iff_exists_zpowers_eq_top.mpr ⟨x, hx⟩)
    obtain ⟨H₁, hH₁, _⟩ := hex (zpowers 1) (hz 1)
    obtain ⟨x, _, hx⟩ :=
      SetLike.exists_of_lt (lt_top_iff_ne_top.mpr hH₁.ne_top)
    obtain ⟨H₂, hH₂, hle⟩ := hex (zpowers x) (hz x)
    refine ⟨H₁, H₂, ?_, hindex hH₁, hindex hH₂⟩
    intro heq
    apply hx
    rw [heq]
    exact hle (by simp)
  · rintro ⟨H₁, H₂, hne, h₁, h₂⟩ hcyc
    letI : IsCyclic G := hcyc
    obtain ⟨g, hg⟩ := isCyclic_iff_exists_zpowers_eq_top.mp hcyc
    have hm (H : Subgroup G) [H.Normal] (x : G) :
        QuotientGroup.mk' H x = 1 ↔ x ∈ H := by
      simp
    have ho (H : Subgroup G) [H.Normal] (hi : H.index = p) :
        orderOf (QuotientGroup.mk' H g) = p := by
      have hd := orderOf_dvd_natCard (QuotientGroup.mk' H g)
      change orderOf (QuotientGroup.mk' H g) ∣ H.index at hd
      rw [hi] at hd
      rcases (Nat.dvd_prime hp.out).mp hd with he | he
      · have hmem : g ∈ H :=
          (hm H g).mp (orderOf_eq_one_iff.mp he)
        have ht : H = ⊤ := by
          apply top_unique
          rw [← hg]
          exact zpowers_le.mpr hmem
        have hp1 : p = 1 := by
          simpa [ht] using hi.symm
        exact (hp.out.ne_one hp1).elim
      · exact he
    have hpow (H : Subgroup G) [H.Normal] (n : ℤ) :
        (QuotientGroup.mk' H g) ^ n = 1 ↔
          (orderOf (QuotientGroup.mk' H g) : ℤ) ∣ n := by
      first
      | exact orderOf_dvd_iff_zpow_eq_one.symm
      | exact zpow_eq_one_iff_dvd
    have ho₁ := ho H₁ h₁
    have ho₂ := ho H₂ h₂
    apply hne
    apply Subgroup.ext
    intro x
    have hx : x ∈ zpowers g := by
      rw [hg]
      trivial
    obtain ⟨n, rfl⟩ := mem_zpowers_iff.mp hx
    rw [← hm H₁ (g ^ n), ← hm H₂ (g ^ n)]
    simp only [map_zpow, hpow, ho₁, ho₂]
