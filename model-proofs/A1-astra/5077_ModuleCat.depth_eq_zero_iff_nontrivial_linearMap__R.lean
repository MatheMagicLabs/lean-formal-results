/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     ModuleCat.depth_eq_zero_iff_nontrivial_linearMap
Source:      Mathlib @ a02a63c2, Mathlib/RingTheory/Depth/Basic.lean, line 200
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

lemma depth_eq_zero_iff_nontrivial_linearMap (N M : ModuleCat.{v} R) :
    N.depth M = 0 ↔ Nontrivial (N →ₗ[R] M) := by
  let e : (N ⟶ M) ≃ (N →ₗ[R] M) :=
    { toFun := fun f => f.hom
      invFun := ModuleCat.ofHom
      left_inv := by intro f; cases f; rfl
      right_inv := by intro f; rfl }
  rw [← (Ext.homEquiv₀.trans e).nontrivial_congr]
  unfold depth
  constructor
  · intro h
    by_contra hn
    letI : Subsingleton (Ext N M 0) :=
      not_nontrivial_iff_subsingleton.mp hn
    have hmem :
        (1 : ℕ∞) ∈
          {n | ∀ i : ℕ, (i : ℕ∞) < n → Subsingleton (Ext N M i)} := by
      intro i hi
      have hi' : i < 1 := by exact_mod_cast hi
      have hi0 : i = 0 := Nat.lt_one_iff.mp hi'
      subst i
      infer_instance
    have hle := le_sSup hmem
    rw [h] at hle
    simpa using hle
  · intro h
    letI := h
    apply le_antisymm
    · apply sSup_le
      intro n hn
      by_contra hnot
      have hpos : (0 : ℕ∞) < n := lt_of_not_ge hnot
      letI : Subsingleton (Ext N M 0) := hn 0 (by simpa using hpos)
      obtain ⟨x, y, hxy⟩ := exists_pair_ne (Ext N M 0)
      exact hxy (Subsingleton.elim x y)
    · exact bot_le
