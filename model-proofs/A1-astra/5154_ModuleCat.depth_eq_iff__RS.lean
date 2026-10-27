/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     ModuleCat.depth_eq_iff
Source:      Mathlib @ a02a63c2, Mathlib/RingTheory/Depth/Basic.lean, line 124
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  A1-astra, arm RS, verified in round 0 (round 0 = first attempt)
Prover:      gpt-6-astra
Setup:       GPT-6 Astra (Codex, effort medium): R = proof plus up to 3 repair rounds with Lean errors; RS = R plus lemma layer; RT = R with read-only Mathlib sources to search; N0-N3 = independent attempts
Check:       the proof replaced the human proof in the Mathlib file above; Lean reported
             0 errors and no `sorry`; sorry/admit/native_decide/search tactics were rejected.
-/

open IsLocalRing LinearMap Module
universe v u
open RingTheory.Sequence Ideal CategoryTheory Abelian Limits Pointwise ModuleCat IsSMulRegular
variable {R : Type u} [CommRing R] [Small.{v} R]
section depth
namespace ModuleCat
open Classical in

lemma depth_eq_iff (N M : ModuleCat.{v} R) (n : ℕ) : N.depth M = n ↔
    Nontrivial (Ext N M n) ∧ ∀ i < n, Subsingleton (Ext N M i) := by
  classical
  constructor
  · intro hn
    have htop : N.depth M < ⊤ := by
      rw [hn]
      simp
    have h := (depth_lt_top_iff N M).mp htop
    have heq : Nat.find h = n := by
      have hc := (depth_eq_find N M h).symm.trans hn
      exact_mod_cast hc
    refine ⟨?_, ?_⟩
    · simpa only [heq] using Nat.find_spec h
    · intro i hi
      apply not_nontrivial_iff_subsingleton.mp
      apply Nat.find_min h
      simpa only [heq] using hi
  · rintro ⟨hn, hlt⟩
    have h : ∃ i, Nontrivial (Ext N M i) := ⟨n, hn⟩
    have heq : Nat.find h = n := by
      apply le_antisymm
      · exact Nat.find_min' h hn
      · by_contra hle
        have hi : Nat.find h < n := Nat.lt_of_not_ge hle
        exact (not_nontrivial_iff_subsingleton.mpr (hlt _ hi))
          (Nat.find_spec h)
    simpa only [heq] using depth_eq_find N M h
