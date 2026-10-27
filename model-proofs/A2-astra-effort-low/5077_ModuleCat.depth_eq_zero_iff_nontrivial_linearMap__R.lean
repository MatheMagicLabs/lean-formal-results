/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     ModuleCat.depth_eq_zero_iff_nontrivial_linearMap
Source:      Mathlib @ a02a63c2, Mathlib/RingTheory/Depth/Basic.lean, line 200
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  A2-astra-effort-low, arm R, verified in round 1 (round 0 = first attempt)
Prover:      gpt-6-astra
Setup:       GPT-6 Astra, reasoning effort low (arms R, N0)
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
  let e : (N ⟶ M) ≃ (N →ₗ[R] M) :=
    { toFun := fun f => f.hom
      invFun := ModuleCat.ofHom
      left_inv := by intro f; rfl
      right_inv := by intro f; rfl }
  have h : Nontrivial (Ext N M 0) ↔ Nontrivial (N →ₗ[R] M) := by
    first
    | exact (Ext.homEquiv₀.trans e).nontrivial_congr
    | exact (Ext.homEquiv₀.symm.trans e).nontrivial_congr
    | exact (Ext.homEquiv.trans e).nontrivial_congr
    | exact (Ext.homEquiv.symm.trans e).nontrivial_congr
  rw [depth]
  constructor
  · intro hz
    apply h.mp
    by_contra hn
    haveI : Subsingleton (Ext N M 0) :=
      not_nontrivial_iff_subsingleton.mp hn
    have h1 :
        (1 : ℕ∞) ≤ sSup {n | ∀ i : ℕ, ↑i < n → Subsingleton (Ext N M i)} := by
      apply le_sSup
      intro i hi
      have hi' : i < 1 := by exact_mod_cast hi
      have : i = 0 := by omega
      subst i
      infer_instance
    rw [hz] at h1
    simpa using h1
  · intro hn
    apply le_antisymm
    · apply sSup_le
      intro n hn'
      by_contra hle
      have hpos : (0 : ℕ∞) < n := lt_of_not_ge hle
      haveI : Subsingleton (Ext N M 0) := hn' 0 (by simpa using hpos)
      haveI : Nontrivial (Ext N M 0) := h.mpr hn
      obtain ⟨a, b, hab⟩ := exists_pair_ne (Ext N M 0)
      exact hab (Subsingleton.elim a b)
    · exact bot_le
