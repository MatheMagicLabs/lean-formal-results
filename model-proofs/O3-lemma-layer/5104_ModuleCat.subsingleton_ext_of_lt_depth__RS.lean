/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     ModuleCat.subsingleton_ext_of_lt_depth
Source:      Mathlib @ a02a63c2, Mathlib/RingTheory/Depth/Basic.lean, line 136
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

lemma subsingleton_ext_of_lt_depth {N M : ModuleCat.{v} R} {i : ℕ}
    (lt : i < N.depth M) : Subsingleton (Ext N M i) := by
  classical
  by_contra hne
  rw [not_subsingleton_iff_nontrivial] at hne
  have h : ∃ n, Nontrivial (Ext N M n) := ⟨i, hne⟩
  rw [depth_eq_find N M h] at lt
  have hlt : ((i : ℕ) : ℕ∞) < ((Nat.find h : ℕ) : ℕ∞) := by convert lt
  have hlt' : i < Nat.find h := by exact_mod_cast hlt
  have hle := Nat.find_min' h hne
  omega
