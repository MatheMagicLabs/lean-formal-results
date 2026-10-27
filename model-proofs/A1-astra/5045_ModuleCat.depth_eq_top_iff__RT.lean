/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     ModuleCat.depth_eq_top_iff
Source:      Mathlib @ a02a63c2, Mathlib/RingTheory/Depth/Basic.lean, line 96
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  A1-astra, arm RT, verified in round 0 (round 0 = first attempt)
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

lemma depth_eq_top_iff (N M : ModuleCat.{v} R) :
    N.depth M = ⊤ ↔ ∀ i, Subsingleton (Ext N M i) := by
  constructor
  · intro h i
    have hi : (i : ℕ∞) < N.depth M := by
      rw [h]
      exact ENat.natCast_lt_top i
    obtain ⟨n, hn, hin⟩ := lt_sSup_iff.mp hi
    exact hn i hin
  · intro h
    apply top_unique
    exact le_sSup (show (⊤ : ℕ∞) ∈
      {n : ℕ∞ | ∀ i : ℕ, i < n → Subsingleton (Ext N M i)} from
        fun i _ ↦ h i)
