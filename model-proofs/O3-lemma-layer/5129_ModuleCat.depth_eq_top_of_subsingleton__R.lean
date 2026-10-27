/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     ModuleCat.depth_eq_top_of_subsingleton
Source:      Mathlib @ a02a63c2, Mathlib/RingTheory/Depth/Basic.lean, line 102
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

lemma depth_eq_top_of_subsingleton (N M : ModuleCat.{v} R) [Subsingleton M] :
    N.depth M = ⊤ := by
  have hM : IsZero M := ModuleCat.isZero_of_subsingleton M
  apply sSup_eq_top.mpr
  intro b hb
  refine ⟨⊤, fun i _ => ?_, hb⟩
  constructor
  intro x y
  rw [← Ext.comp_mk₀_id x, ← Ext.comp_mk₀_id y, hM.eq_of_src (𝟙 M) 0, Ext.mk₀_zero,
    Ext.comp_zero, Ext.comp_zero]
