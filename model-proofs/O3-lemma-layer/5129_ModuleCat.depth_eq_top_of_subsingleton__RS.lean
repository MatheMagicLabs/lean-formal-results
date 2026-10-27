/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     ModuleCat.depth_eq_top_of_subsingleton
Source:      Mathlib @ a02a63c2, Mathlib/RingTheory/Depth/Basic.lean, line 102
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  O3-lemma-layer, arm RS, verified in round 0 (round 0 = first attempt)
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

lemma depth_eq_top_of_subsingleton (N M : ModuleCat.{v} R) [Subsingleton M] :
    N.depth M = ⊤ := by
  rw [ModuleCat.depth_eq_top_iff]
  intro i
  constructor
  intro a b
  have h : 𝟙 M = 0 := (ModuleCat.isZero_of_subsingleton M).eq_of_src _ _
  rw [← a.comp_mk₀_id, ← b.comp_mk₀_id, h, Ext.mk₀_zero, Ext.comp_zero, Ext.comp_zero]
