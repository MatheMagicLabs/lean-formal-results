/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     IsPGroup.isCoatom_iff_index_eq_prime
Source:      Mathlib @ a02a63c2, Mathlib/GroupTheory/Nilpotent.lean, line 1261
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  A1-astra, arm N1, verified in round 0 (round 0 = first attempt)
Prover:      gpt-6-astra
Setup:       GPT-6 Astra (Codex, effort medium): R = proof plus up to 3 repair rounds with Lean errors; RS = R plus lemma layer; RT = R with read-only Mathlib sources to search; N0-N3 = independent attempts
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
  have hiff : IsCoatom H ↔ H.index.Prime := by
    first
    | exact Subgroup.isCoatom_iff_index_prime
    | exact Subgroup.isCoatom_iff_index_prime H
    | exact Subgroup.isCoatom_iff_prime_index
    | exact Subgroup.isCoatom_iff_prime_index H
  rw [hiff]
  constructor
  · intro h
    letI : H.FiniteIndex := ⟨h.ne_zero⟩
    have hpow : ∃ n : ℕ, H.index = p ^ n := by
      first
      | exact hG.index H
      | exact hG.exists_index_eq H
      | exact hG.index_eq_prime_pow H
      | exact (hG.index H).resolve_left h.ne_zero
    obtain ⟨n, hn⟩ := hpow
    have hdvd : p ∣ H.index := by
      cases n with
      | zero =>
          simp only [pow_zero] at hn
          exact (h.ne_one hn).elim
      | succ n =>
          rw [hn, pow_succ]
          exact dvd_mul_left p (p ^ n)
    rcases (Nat.dvd_prime h).mp hdvd with hpone | heq
    · exact (hp.out.ne_one hpone).elim
    · exact heq.symm
  · intro h
    simpa only [h] using hp.out
