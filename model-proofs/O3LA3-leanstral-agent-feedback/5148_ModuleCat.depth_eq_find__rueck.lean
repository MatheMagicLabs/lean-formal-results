/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     ModuleCat.depth_eq_find
Source:      Mathlib @ a02a63c2, Mathlib/RingTheory/Depth/Basic.lean, line 84
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  O3LA3-leanstral-agent-feedback, arm rueck, verified in final
Prover:      labs-leanstral-1-5
Setup:       Leanstral 1.5 agent with goal-state feedback (arm rueck)
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
  set m := Nat.find h with hm
  have hm_spec : Nontrivial (Ext N M m) := Nat.find_spec h
  have hm_min : ∀ {n : ℕ}, n < m → ¬ Nontrivial (Ext N M n) := fun {n} hn ↦ Nat.find_min h hn
  set S : Set ℕ∞ := {n | ∀ i : ℕ, i < n → Subsingleton (Ext N M i)} with hS
  have hm_mem : (m : ℕ∞) ∈ S := by
    rw [hS]
    intro i hi
    have hi_nat : (i : ℕ) < m := by
      simpa [Nat.cast_lt] using hi
    have h_not_nontriv : ¬ Nontrivial (Ext N M i) := hm_min hi_nat
    exact (not_nontrivial_iff_subsingleton.mp h_not_nontriv)
  have h_upper : ∀ x ∈ S, x ≤ (m : ℕ∞) := by
    intro x hx
    by_contra! hlt
    have hx_mem := hx
    rw [hS] at hx_mem
    have h_sub : Subsingleton (Ext N M m) := hx_mem m hlt
    have h_not_nontriv : ¬ Nontrivial (Ext N M m) :=
      (not_nontrivial_iff_subsingleton.mpr h_sub)
    exact h_not_nontriv hm_spec
  have h_bdd : BddAbove S := ⟨(m : ℕ∞), h_upper⟩
  apply le_antisymm
  · -- N.depth M ≤ m
    rw [ModuleCat.depth, ← hS]
    exact csSup_le ⟨(m : ℕ∞), hm_mem⟩ h_upper
  · -- m ≤ N.depth M
    rw [ModuleCat.depth, ← hS]
    exact le_csSup h_bdd hm_mem
