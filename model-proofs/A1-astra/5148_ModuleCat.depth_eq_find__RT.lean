/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     ModuleCat.depth_eq_find
Source:      Mathlib @ a02a63c2, Mathlib/RingTheory/Depth/Basic.lean, line 84
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

private lemma depth_eq_find (N M : ModuleCat.{v} R) (h : ∃ n, Nontrivial (Ext N M n)) :
    N.depth M = Nat.find h := by
  unfold ModuleCat.depth
  apply le_antisymm
  · apply sSup_le
    intro n hn
    by_contra hle
    exact (not_nontrivial_iff_subsingleton.mpr
      (hn (Nat.find h) (lt_of_not_ge hle))) (Nat.find_spec h)
  · apply le_sSup
    intro i hi
    exact not_nontrivial_iff_subsingleton.mp
      (Nat.find_min h (ENat.natCast_lt_natCast.mp hi))
