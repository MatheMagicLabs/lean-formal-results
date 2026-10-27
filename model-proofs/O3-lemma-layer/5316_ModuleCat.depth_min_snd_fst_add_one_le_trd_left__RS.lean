/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     ModuleCat.depth_min_snd_fst_add_one_le_trd_left
Source:      Mathlib @ a02a63c2, Mathlib/RingTheory/Depth/Basic.lean, line 245
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  O3-lemma-layer, arm RS, verified in round 1 (round 0 = first attempt)
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

lemma depth_min_snd_fst_add_one_le_trd_left
    (S : ShortComplex (ModuleCat.{v} R)) (hS : S.ShortExact) (N : ModuleCat.{v} R) :
    S.X₂.depth N ⊓ (S.X₁.depth N + 1) ≤ S.X₃.depth N := by
  have key : ∀ (X : ModuleCat.{v} R) (i : ℕ), (i : ℕ∞) < X.depth N →
      Subsingleton (Ext X N i) := by
    intro X i hi
    unfold ModuleCat.depth at hi
    obtain ⟨n, hn, hin⟩ := lt_sSup_iff.mp hi
    exact hn i hin
  refine le_sSup ?_
  intro i hi
  rw [lt_inf_iff] at hi
  obtain ⟨h2, h1⟩ := hi
  have hz : ∀ x : Ext S.X₃ N i, x = 0 := by
    rcases i with _ | j
    · intro x
      obtain ⟨f, rfl⟩ := (Ext.mk₀_bijective ..).2 x
      have h : (Ext.mk₀ S.g).comp (Ext.mk₀ f) (zero_add 0) = 0 := by
        haveI := key S.X₂ 0 h2
        exact Subsingleton.elim _ _
      rw [Ext.mk₀_comp_mk₀] at h
      have hf : f = 0 := by
        have hg : S.g ≫ f = 0 := (Ext.mk₀_eq_zero_iff _).1 h
        haveI := hS.epi_g
        exact (cancel_epi S.g).1 (by rw [hg, Limits.comp_zero])
      rw [hf, Ext.mk₀_zero]
    · have h1' : (j : ℕ∞) < S.X₁.depth N := by
        by_contra hc
        push_neg at hc
        have : S.X₁.depth N + 1 ≤ ((j+1 : ℕ) : ℕ∞) := by
          push_cast
          exact add_le_add hc le_rfl
        exact absurd h1 (not_lt.2 this)
      intro x
      have hx : (Ext.mk₀ S.g).comp x (zero_add (j+1)) = 0 := by
        haveI := key S.X₂ (j+1) h2
        exact Subsingleton.elim _ _
      obtain ⟨x₁, rfl⟩ := Ext.contravariant_sequence_exact₃ hS N x hx
        (show 1 + j = j + 1 by omega)
      haveI := key S.X₁ j h1'
      rw [Subsingleton.elim x₁ 0]
      simp
  exact ⟨fun a b => (hz a).trans (hz b).symm⟩
