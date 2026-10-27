/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     ModuleCat.depth_eq_top_of_subsingleton
Source:      Mathlib @ a02a63c2, Mathlib/RingTheory/Depth/Basic.lean, line 102
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  O4-layer-with-search, arm RT, verified in round 0 (round 0 = first attempt)
Prover:      claude-opus-5-5
Setup:       Opus 5.5 with repair loop, lemma layer and name search (arm RT)
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
  rw [depth_eq_top_iff]
  intro i
  have hM : IsZero M := ModuleCat.isZero_of_subsingleton M
  have h1 : (𝟙 M) = 0 := hM.eq_of_src _ _
  refine ⟨fun a b => ?_⟩
  rw [← Ext.comp_mk₀_id a, ← Ext.comp_mk₀_id b, h1, Ext.mk₀_zero, Ext.comp_zero,
    Ext.comp_zero]
