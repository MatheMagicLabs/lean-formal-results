/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     ModuleCat.depth_eq_zero_iff_nontrivial_linearMap
Source:      Mathlib @ a02a63c2, Mathlib/RingTheory/Depth/Basic.lean, line 200
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  O3-lemma-layer, arm R, verified in round 1 (round 0 = first attempt)
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
  have e : Nontrivial (Ext N M 0) ↔ Nontrivial (N →ₗ[R] M) := by
    have f : Ext N M 0 ≃ (N →ₗ[R] M) :=
      Ext.addEquiv₀.toEquiv.trans ModuleCat.homEquiv
    exact ⟨fun _ => f.symm.nontrivial, fun _ => f.nontrivial⟩
  rw [← e]
  simp only [depth]
  constructor
  · intro h
    by_contra hn
    have hs : Subsingleton (Ext N M 0) := not_nontrivial_iff_subsingleton.mp hn
    have h1 : (1 : ℕ∞) ∈ {n : ℕ∞ | ∀ i : ℕ, (i : ℕ∞) < n → Subsingleton (Ext N M i)} := by
      rw [Set.mem_setOf_eq]
      intro i hi
      have hi' : i < 1 := by exact_mod_cast hi
      obtain rfl : i = 0 := by omega
      exact hs
    have h2 := le_sSup h1
    rw [h] at h2
    exact absurd h2 (by norm_num)
  · intro h
    apply le_antisymm _ (by simp)
    apply sSup_le
    intro n hn
    by_contra hne
    have hpos : (0 : ℕ∞) < n := not_le.mp hne
    have hsub := hn 0 (by simpa using hpos)
    obtain ⟨x, y, hxy⟩ := h.exists_pair_ne
    exact hxy (Subsingleton.elim x y)
