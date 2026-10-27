/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     ModuleCat.depth_min_snd_fst_add_one_le_trd_left
Source:      Mathlib @ a02a63c2, Mathlib/RingTheory/Depth/Basic.lean, line 245
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  O3-lemma-layer, arm R, verified in round 2 (round 0 = first attempt)
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
  have hz : ∀ {A B : ModuleCat.{v} R}, (Ext.mk₀ (0 : A ⟶ B) : Ext A B 0) = 0 := by
    intro A B
    first
      | simpa using (Ext.mk₀_add (0 : A ⟶ B) 0)
      | simp
      | exact map_zero (Ext.addEquiv₀ (X := A) (Y := B)).symm
  unfold ModuleCat.depth
  apply le_sSup
  intro i hi
  rw [lt_inf_iff] at hi
  obtain ⟨hi1, hi2⟩ := hi
  obtain ⟨m, hm, him⟩ := lt_sSup_iff.1 hi1
  have s2 := hm i him
  refine subsingleton_of_forall_eq 0 fun x₃ => ?_
  have h0 : (Ext.mk₀ S.g).comp x₃ (zero_add i) = 0 := Subsingleton.elim _ _
  cases i with
  | zero =>
    obtain ⟨f, rfl⟩ := (Ext.mk₀_bijective _ _).2 x₃
    rw [Ext.mk₀_comp_mk₀] at h0
    have hf : S.g ≫ f = 0 := (Ext.mk₀_bijective _ _).1 (h0.trans hz.symm)
    have := hS.epi_g
    have hf' : f = 0 := (cancel_epi S.g).1 (hf.trans (Limits.comp_zero).symm)
    rw [hf', hz]
  | succ n =>
    obtain ⟨x₁, hx₁⟩ := Ext.contravariant_sequence_exact₃ (Y := N) (hS := hS) (x₃ := x₃)
      (hx₃ := h0) (n₀ := n) (hn₀ := by omega)
    push_cast at hi2
    have h3 := not_le.1 fun h => (not_le.2 hi2) (add_le_add h le_rfl)
    obtain ⟨m', hm', hm'n⟩ := lt_sSup_iff.1 h3
    have s1 := hm' n hm'n
    rw [← hx₁, Subsingleton.elim x₁ 0, Ext.comp_zero]
