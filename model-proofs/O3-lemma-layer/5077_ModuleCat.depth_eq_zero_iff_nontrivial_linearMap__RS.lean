/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     ModuleCat.depth_eq_zero_iff_nontrivial_linearMap
Source:      Mathlib @ a02a63c2, Mathlib/RingTheory/Depth/Basic.lean, line 200
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

lemma depth_eq_zero_iff_nontrivial_linearMap (N M : ModuleCat.{v} R) :
    N.depth M = 0 ↔ Nontrivial (N →ₗ[R] M) := by
  have e : Ext N M 0 ≃ (N →ₗ[R] M) :=
    (Ext.homEquiv₀).trans
      { toFun := fun f => f.hom
        invFun := fun f => ModuleCat.ofHom f
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
  rw [← (Nat.cast_zero (R := ℕ∞)), depth_eq_iff]
  constructor
  · rintro ⟨h, -⟩
    exact e.symm.nontrivial
  · intro h
    exact ⟨e.nontrivial, fun i hi => absurd hi (Nat.not_lt_zero _)⟩
