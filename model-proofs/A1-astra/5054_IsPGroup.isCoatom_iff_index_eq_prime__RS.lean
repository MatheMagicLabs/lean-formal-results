/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     IsPGroup.isCoatom_iff_index_eq_prime
Source:      Mathlib @ a02a63c2, Mathlib/GroupTheory/Nilpotent.lean, line 1261
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  A1-astra, arm RS, verified in round 0 (round 0 = first attempt)
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
  rw [H.isCoatom_iff_index_prime]
  constructor
  · intro hH
    letI : H.FiniteIndex := ⟨hH.ne_zero⟩
    obtain ⟨n, hn⟩ := hG.index H
    have hd : H.index ∣ p ^ n := by rw [← hn]
    rcases (Nat.dvd_prime hp.out).mp (hH.dvd_of_dvd_pow hd) with h | h
    · exact (hH.ne_one h).elim
    · exact h
  · intro h
    simpa [h] using hp.out
