/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     ModuleCat.depth_eq_find
Source:      Mathlib @ a02a63c2, Mathlib/RingTheory/Depth/Basic.lean, line 84
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  O3-lemma-layer, arm RS, verified in round 1 (round 0 = first attempt)
Prover:      claude-opus-5-5
Setup:       Opus 5.5 with repair loop: arm R = repair only; arm RS = repair plus the Lean-checked lemma layer
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
  unfold ModuleCat.depth
  apply le_antisymm
  · apply sSup_le
    intro n hn
    simp only [Set.mem_setOf_eq] at hn
    by_contra hlt
    push_neg at hlt
    have h1 := hn (Nat.find h) hlt
    have h2 := Nat.find_spec h
    exact not_nontrivial_iff_subsingleton.mpr h1 h2
  · apply le_sSup
    simp only [Set.mem_setOf_eq]
    intro i hi
    have hi' : i < Nat.find h := by exact_mod_cast hi
    exact not_nontrivial_iff_subsingleton.mp (Nat.find_min h hi')
