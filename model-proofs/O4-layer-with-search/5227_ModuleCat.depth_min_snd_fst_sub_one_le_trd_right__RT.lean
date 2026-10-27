/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     ModuleCat.depth_min_snd_fst_sub_one_le_trd_right
Source:      Mathlib @ a02a63c2, Mathlib/RingTheory/Depth/Basic.lean, line 300
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  O4-layer-with-search, arm RT, verified in round 0 (round 0 = first attempt)
Prover:      claude-opus-5-5
Setup:       Opus 5.5 with repair loop, lemma layer and name search (arm RT)
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

@[stacks 00LX "(2)"]
lemma depth_min_snd_fst_sub_one_le_trd_right
    (N : ModuleCat.{v} R) (S : ShortComplex (ModuleCat.{v} R)) (hS : S.ShortExact) :
    N.depth S.X₂ ⊓ (N.depth S.X₁ - 1) ≤ N.depth S.X₃ := by
  have key : ∀ (M : ModuleCat.{v} R) (i : ℕ), (i : ℕ∞) < N.depth M →
      Subsingleton (Ext N M i) := by
    intro M i hi
    by_cases h : N.depth M = ⊤
    · exact (N.depth_eq_top_iff M).1 h i
    · obtain ⟨m, hm⟩ := ENat.ne_top_iff_exists.mp h
      rw [← hm] at hi
      exact ((N.depth_eq_iff M m).1 hm.symm).2 i (by exact_mod_cast hi)
  by_contra hlt
  push_neg at hlt
  have hne : N.depth S.X₃ ≠ ⊤ := ne_top_of_lt hlt
  obtain ⟨k, hk⟩ := ENat.ne_top_iff_exists.mp hne
  have hnt := ((N.depth_eq_iff S.X₃ k).1 hk.symm).1
  rw [← hk] at hlt
  have h2 : (k : ℕ∞) < N.depth S.X₂ := lt_of_lt_of_le hlt inf_le_left
  have h1' : (k : ℕ∞) < N.depth S.X₁ - 1 := lt_of_lt_of_le hlt inf_le_right
  have h1 : ((k + 1 : ℕ) : ℕ∞) < N.depth S.X₁ := by
    push_cast
    exact lt_tsub_iff_right.mp h1'
  haveI := key S.X₂ k h2
  haveI := key S.X₁ (k + 1) h1
  have hall : ∀ z : Ext N S.X₃ k, z = 0 := by
    intro z
    obtain ⟨x₂, hx₂⟩ := Ext.covariant_sequence_exact₃ (X := N) (hS := hS) z
      (n₁ := k + 1) rfl (Subsingleton.elim _ _)
    rw [← hx₂, Subsingleton.elim x₂ 0, Ext.zero_comp]
  obtain ⟨x, y, hxy⟩ := hnt
  exact hxy (by rw [hall x, hall y])
