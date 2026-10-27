/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     ModuleCat.depth_eq_of_iso_right
Source:      Mathlib @ a02a63c2, Mathlib/RingTheory/Depth/Basic.lean, line 184
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

lemma depth_eq_of_iso_right (N : ModuleCat.{v} R) {M M' : ModuleCat.{v} R} (e : M ≅ M') :
    N.depth M = N.depth M' := by
  simp only [ModuleCat.depth]
  congr 1
  ext n
  apply forall_congr'
  intro i
  apply imp_congr_right
  intro _
  constructor
  · intro h
    exact Function.Injective.subsingleton
      (f := fun y : Ext N M' i => y.comp (Ext.mk₀ e.inv) (add_zero i))
      (by
        intro a b hab
        have := congrArg (fun x => x.comp (Ext.mk₀ e.hom) (add_zero i)) hab
        simpa [Ext.comp_assoc_of_second_deg_zero, Ext.mk₀_comp_mk₀] using this)
  · intro h
    exact Function.Injective.subsingleton
      (f := fun y : Ext N M i => y.comp (Ext.mk₀ e.hom) (add_zero i))
      (by
        intro a b hab
        have := congrArg (fun x => x.comp (Ext.mk₀ e.inv) (add_zero i)) hab
        simpa [Ext.comp_assoc_of_second_deg_zero, Ext.mk₀_comp_mk₀] using this)
