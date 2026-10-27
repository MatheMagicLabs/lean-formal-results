/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     ModuleCat.depth_eq_find
Source:      Mathlib @ a02a63c2, Mathlib/RingTheory/Depth/Basic.lean, line 84
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  LS1-leanstral-loop, arm L1, verified in round 3 (round 0 = first attempt)
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

private lemma depth_eq_find (N M : ModuleCat.{v} R) (h : ∃ n, Nontrivial (Ext N M n)) :
    N.depth M = Nat.find h := by
  rw [ModuleCat.depth]
  set a := (Nat.find h : ℕ∞) with ha
  have h_eq : {n : ℕ∞ | ∀ i : ℕ, i < n → Subsingleton (Ext N M i)} = Set.Iic a := by
    ext n
    constructor
    · intro hn
      by_contra! hlt
      have ha_lt_n : a < n := lt_of_not_ge hlt
      have hsub := hn (Nat.find h) ha_lt_n
      have hnon : Nontrivial (Ext N M (Nat.find h)) := Nat.find_spec h
      exact not_subsingleton (α := Ext N M (Nat.find h)) hsub
    · intro hn
      intro i hi
      have hi_lt_a : (i : ℕ∞) < a := lt_of_lt_of_le hi hn
      have hi_lt : i < Nat.find h := by
        simpa [ha] using hi_lt_a
      have h_not_nontrivial : ¬ Nontrivial (Ext N M i) :=
        ((Nat.lt_find_iff h i).mp hi_lt) i (le_refl i)
      exact not_nontrivial_iff_subsingleton.mp h_not_nontrivial
  rw [h_eq]
  exact csSup_Iic
