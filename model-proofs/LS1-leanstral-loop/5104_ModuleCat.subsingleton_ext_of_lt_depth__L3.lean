/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     ModuleCat.subsingleton_ext_of_lt_depth
Source:      Mathlib @ a02a63c2, Mathlib/RingTheory/Depth/Basic.lean, line 136
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  LS1-leanstral-loop, arm L3, verified in round 3 (round 0 = first attempt)
Prover:      labs-leanstral-1-5
Setup:       Leanstral 1.5 in a fixed check-and-repair loop: L1 = 1 candidate per round, L3 = up to 3
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

lemma subsingleton_ext_of_lt_depth {N M : ModuleCat.{v} R} {i : ℕ}
    (lt : i < N.depth M) : Subsingleton (Ext N M i) := by
  classical
  by_cases htop : N.depth M = ⊤
  · have h := (depth_eq_top_iff N M).mp htop
    exact h i
  · have hlt : N.depth M < ⊤ := lt_of_le_of_ne le_top htop
    have hex := (depth_lt_top_iff N M).mp hlt
    have h_find := depth_eq_find N M hex
    have hi_lt_find : i < Nat.find hex := by
      have : (i : ℕ∞) < N.depth M := lt
      rw [h_find] at this
      exact_mod_cast this
    have h_not_nontrivial := Nat.find_min hex hi_lt_find
    exact not_nontrivial_iff_subsingleton.mp h_not_nontrivial
