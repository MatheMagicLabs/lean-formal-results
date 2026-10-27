/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     ModuleCat.depth_eq_find
Source:      Mathlib @ a02a63c2, Mathlib/RingTheory/Depth/Basic.lean, line 84
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  A2-astra-effort-low, arm R, verified in round 3 (round 0 = first attempt)
Prover:      gpt-6-astra
Setup:       GPT-6 Astra, reasoning effort low (arms R, N0)
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

private lemma depth_eq_find (N M : ModuleCat.{v} R) (h : ∃ n, Nontrivial (Ext N M n)) :
    N.depth M = Nat.find h := by
  classical
  change sSup {n : ℕ∞ | ∀ i : ℕ, (i : ℕ∞) < n →
    Subsingleton (Ext N M i)} = ↑(Nat.find h)
  apply le_antisymm
  · apply sSup_le
    intro n hn
    apply le_of_not_gt
    intro hlt
    exact (not_nontrivial_iff_subsingleton.mpr
      (hn (Nat.find h) hlt)) (Nat.find_spec h)
  · apply le_sSup
    intro i hi
    apply not_nontrivial_iff_subsingleton.mp
    apply Nat.find_min h
    exact_mod_cast hi
