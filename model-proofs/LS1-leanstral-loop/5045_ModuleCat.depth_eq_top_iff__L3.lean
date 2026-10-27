/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     ModuleCat.depth_eq_top_iff
Source:      Mathlib @ a02a63c2, Mathlib/RingTheory/Depth/Basic.lean, line 96
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  LS1-leanstral-loop, arm L3, verified in round 1 (round 0 = first attempt)
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

lemma depth_eq_top_iff (N M : ModuleCat.{v} R) :
    N.depth M = ⊤ ↔ ∀ i, Subsingleton (Ext N M i) := by
  constructor
  · intro h i
    by_contra hni
    have hnontriv : Nontrivial (Ext N M i) := by
      by_contra hnot
      have hsub : Subsingleton (Ext N M i) := not_nontrivial_iff_subsingleton.mp hnot
      exact hni hsub
    have hfind := depth_eq_find N M ⟨i, hnontriv⟩
    rw [h] at hfind
    exact ENat.coe_ne_top _ hfind.symm
  · intro h
    apply ENat.eq_top_iff_forall_gt.mpr
    intro m
    have hbdd : BddAbove {n : ℕ∞ | ∀ i : ℕ, i < n → Subsingleton (Ext N M i)} := by
      refine ⟨⊤, λ x hx => le_top⟩
    have hmem : (m+1 : ℕ∞) ∈ {n : ℕ∞ | ∀ i : ℕ, i < n → Subsingleton (Ext N M i)} := by
      intro i hi
      exact h i
    have hle : (m+1 : ℕ∞) ≤ N.depth M := by
      simpa [ModuleCat.depth] using le_csSup hbdd hmem
    have hm : (m : ℕ∞) < (m+1 : ℕ∞) := by
      exact ENat.coe_lt_coe.mpr (Nat.lt_succ_self m)
    exact lt_of_lt_of_le hm hle
