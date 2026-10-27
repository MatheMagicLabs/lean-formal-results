/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     ModuleCat.depth_eq_sSup_lt_top
Source:      Mathlib @ a02a63c2, Mathlib/RingTheory/Depth/Basic.lean, line 144
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  A1-astra, arm R, verified in round 0 (round 0 = first attempt)
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

lemma depth_eq_sSup_lt_top (N M : ModuleCat.{v} R) : N.depth M =
    sSup {n : ℕ∞ | n < ⊤ ∧ ∀ i : ℕ, i < n → Subsingleton (Ext N M i)} := by
  classical
  first
  | change sSup {n : ℕ∞ | ∀ i : ℕ, i < n →
      Subsingleton (Ext N M i)} = _
  | rw [depth_eq_sSup]
  apply le_antisymm
  · refine sSup_le fun n hn => ?_
    by_contra h
    have hlt :
        sSup {n : ℕ∞ | n < ⊤ ∧ ∀ i : ℕ, i < n →
          Subsingleton (Ext N M i)} < n := lt_of_not_ge h
    have hne := ne_top_of_lt hlt
    generalize hs :
      sSup {n : ℕ∞ | n < ⊤ ∧ ∀ i : ℕ, i < n →
        Subsingleton (Ext N M i)} = s at *
    lift s to ℕ using hne with k
    have hmem :
        (↑(k + 1) : ℕ∞) ∈
          {n : ℕ∞ | n < ⊤ ∧ ∀ i : ℕ, i < n →
            Subsingleton (Ext N M i)} := by
      refine ⟨by simp, ?_⟩
      intro i hi
      apply hn i
      have hik : i < k + 1 := by exact_mod_cast hi
      have hik' : (i : ℕ∞) ≤ k := by
        exact_mod_cast Nat.le_of_lt_succ hik
      exact lt_of_le_of_lt hik' hlt
    have hk := le_sSup hmem
    rw [hs] at hk
    have hk' : k + 1 ≤ k := by exact_mod_cast hk
    omega
  · exact sSup_le_sSup fun n hn => hn.2
