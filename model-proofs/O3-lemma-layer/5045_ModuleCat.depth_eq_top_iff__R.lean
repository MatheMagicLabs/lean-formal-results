/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     ModuleCat.depth_eq_top_iff
Source:      Mathlib @ a02a63c2, Mathlib/RingTheory/Depth/Basic.lean, line 96
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  O3-lemma-layer, arm R, verified in round 0 (round 0 = first attempt)
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

lemma depth_eq_top_iff (N M : ModuleCat.{v} R) :
    N.depth M = ⊤ ↔ ∀ i, Subsingleton (Ext N M i) := by
  constructor
  · intro h i
    rw [depth, sSup_eq_top] at h
    obtain ⟨n, hn, hlt⟩ := h ((i + 1 : ℕ) : ℕ∞) (ENat.coe_lt_top _)
    exact hn i (lt_trans (by exact_mod_cast Nat.lt_succ_self i) hlt)
  · intro h
    rw [depth]
    apply le_antisymm le_top
    apply le_sSup
    exact fun i _ => h i
