/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     ModuleCat.depth_eq_of_iso_right
Source:      Mathlib @ a02a63c2, Mathlib/RingTheory/Depth/Basic.lean, line 184
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  A2-astra-effort-high, arm N0, verified in round 0 (round 0 = first attempt)
Prover:      gpt-6-astra
Setup:       GPT-6 Astra, reasoning effort high (arms R, N0)
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
  let E (i : ℕ) : Ext N M i ≃ Ext N M' i :=
    { toFun := fun x => x.comp (Ext.mk₀ e.hom) (by simp)
      invFun := fun x => x.comp (Ext.mk₀ e.inv) (by simp)
      left_inv := by
        intro x
        simp [Ext.comp_assoc]
      right_inv := by
        intro x
        simp [Ext.comp_assoc] }
  have hs (i : ℕ) :
      Subsingleton (Ext N M i) ↔ Subsingleton (Ext N M' i) :=
    (E i).subsingleton_congr
  have hn (i : ℕ) :
      Nontrivial (Ext N M i) ↔ Nontrivial (Ext N M' i) :=
    (E i).nontrivial_congr
  simp only [depth, hs, hn]
