/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     ModuleCat.depth_eq_zero_iff_nontrivial_linearMap
Source:      Mathlib @ a02a63c2, Mathlib/RingTheory/Depth/Basic.lean, line 200
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  A1-astra, arm RS, verified in round 1 (round 0 = first attempt)
Prover:      gpt-6-astra
Setup:       GPT-6 Astra (Codex, effort medium): R = proof plus up to 3 repair rounds with Lean errors; RS = R plus lemma layer; RT = R with read-only Mathlib sources to search; N0-N3 = independent attempts
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

lemma depth_eq_zero_iff_nontrivial_linearMap (N M : ModuleCat.{v} R) :
    N.depth M = 0 ↔ Nontrivial (N →ₗ[R] M) := by
  have hd : N.depth M = 0 ↔ Nontrivial (Ext N M 0) := by
    simpa using (depth_eq_iff N M 0)
  let e₀ : Ext N M 0 ≃ (N ⟶ M) := Ext.homEquiv₀
  let e : (N ⟶ M) ≃ (N →ₗ[R] M) :=
    { toFun := fun f => f.hom
      invFun := fun f => ofHom f
      left_inv := by intro f; rfl
      right_inv := by intro f; rfl }
  exact hd.trans (e₀.nontrivial_congr.trans e.nontrivial_congr)
