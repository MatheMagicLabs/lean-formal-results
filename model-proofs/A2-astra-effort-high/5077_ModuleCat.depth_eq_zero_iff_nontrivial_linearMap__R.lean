/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     ModuleCat.depth_eq_zero_iff_nontrivial_linearMap
Source:      Mathlib @ a02a63c2, Mathlib/RingTheory/Depth/Basic.lean, line 200
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  A2-astra-effort-high, arm R, verified in round 1 (round 0 = first attempt)
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

lemma depth_eq_zero_iff_nontrivial_linearMap (N M : ModuleCat.{v} R) :
    N.depth M = 0 ↔ Nontrivial (N →ₗ[R] M) := by
  let e₀ : Ext N M 0 ≃ (N ⟶ M) :=
    ⟨Ext.homEquiv₀, Ext.homEquiv₀.symm,
      Ext.homEquiv₀.left_inv, Ext.homEquiv₀.right_inv⟩
  let e₁ : (N ⟶ M) ≃ (N →ₗ[R] M) :=
    { toFun := fun f => f.hom
      invFun := fun f => ModuleCat.ofHom f
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  let S : Set ℕ∞ :=
    {n | ∀ i : ℕ, (i : ℕ∞) < n → Subsingleton (Ext N M i)}
  change sSup S = 0 ↔ Nontrivial (N →ₗ[R] M)
  rw [← (e₀.trans e₁).nontrivial_congr]
  constructor
  · intro hd
    apply not_subsingleton_iff_nontrivial.mp
    intro hs
    have hmem : (1 : ℕ∞) ∈ S := by
      intro i hi
      have hi' : i < 1 := by exact_mod_cast hi
      have hi0 : i = 0 := by omega
      subst i
      exact hs
    have hle : (1 : ℕ∞) ≤ sSup S := le_sSup hmem
    rw [hd] at hle
    simpa using hle
  · intro h
    apply le_antisymm
    · apply sSup_le
      intro n hn
      by_contra hn'
      have hpos : (0 : ℕ∞) < n := lt_of_not_ge hn'
      have hs : Subsingleton (Ext N M 0) :=
        hn 0 (by simpa using hpos)
      exact (not_subsingleton_iff_nontrivial.mpr h) hs
    · exact bot_le
