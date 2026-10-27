/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     ModuleCat.depth_eq_of_iso_right
Source:      Mathlib @ a02a63c2, Mathlib/RingTheory/Depth/Basic.lean, line 184
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  A1-astra, arm R, verified in round 2 (round 0 = first attempt)
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

lemma depth_eq_of_iso_right (N : ModuleCat.{v} R) {M M' : ModuleCat.{v} R} (e : M ≅ M') :
    N.depth M = N.depth M' := by
  have h (i : ℕ) : Subsingleton (Ext N M i) ↔ Subsingleton (Ext N M' i) := by
    let f : Ext N M i ≃ Ext N M' i :=
      { toFun := fun x => x.comp (Ext.mk₀ e.hom) (Nat.add_zero i)
        invFun := fun x => x.comp (Ext.mk₀ e.inv) (Nat.add_zero i)
        left_inv := by
          intro x
          first
          | simpa [Ext.comp_assoc]
          | simpa [← Ext.comp_assoc]
        right_inv := by
          intro x
          first
          | simpa [Ext.comp_assoc]
          | simpa [← Ext.comp_assoc] }
    constructor
    · intro h
      letI := h
      exact f.symm.injective.subsingleton
    · intro h
      letI := h
      exact f.injective.subsingleton
  simp only [depth, h]
