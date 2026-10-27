/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     ModuleCat.depth_eq_zero_iff_nontrivial_linearMap
Source:      Mathlib @ a02a63c2, Mathlib/RingTheory/Depth/Basic.lean, line 200
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  E1-repair-decomposition, arm V, verified in round 2 (round 0 = first attempt)
Prover:      gpt-6-astra
Setup:       GPT-6 Astra, which part of Lean feedback makes repair work: after a shared first attempt (E0), V = full error messages, Z = line numbers only, B = only "Lean rejected this proof"
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
  classical
  have hdepth : N.depth M = 0 ↔ Nontrivial (Ext N M 0) := by
    constructor
    · intro h
      rcases subsingleton_or_nontrivial (Ext N M 0) with hs | hn
      · letI := hs
        have hle : 1 ≤ N.depth M := by
          apply le_sSup
          intro i hi
          have hi' : i < 1 := by exact_mod_cast hi
          have hi0 : i = 0 := Nat.lt_one_iff.mp hi'
          subst i
          infer_instance
        rw [h] at hle
        exact False.elim (by simpa using hle)
      · exact hn
    · intro h
      letI := h
      apply le_antisymm _ zero_le
      apply sSup_le
      intro n hn
      by_contra hle
      have hp : 0 < n := lt_of_not_ge hle
      letI : Subsingleton (Ext N M 0) := hn 0 (by simpa using hp)
      obtain ⟨x, y, hxy⟩ := exists_pair_ne (Ext N M 0)
      exact hxy (Subsingleton.elim x y)
  let e₀ : Ext N M 0 ≃ (N ⟶ M) :=
    { toFun := fun x => Ext.homEquiv₀ x
      invFun := fun x => Ext.homEquiv₀.symm x
      left_inv := fun x => Ext.homEquiv₀.symm_apply_apply x
      right_inv := fun x => Ext.homEquiv₀.apply_symm_apply x }
  let e : (N ⟶ M) ≃ (N →ₗ[R] M) :=
    { toFun := fun f => f.hom
      invFun := fun f => ModuleCat.ofHom f
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  exact hdepth.trans (e₀.nontrivial_congr.trans e.nontrivial_congr)
