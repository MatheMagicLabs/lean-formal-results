/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     ModuleCat.depth_min_fst_trd_le_snd_right
Source:      Mathlib @ a02a63c2, Mathlib/RingTheory/Depth/Basic.lean, line 264
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

@[stacks 00LX "(1)"]
lemma depth_min_fst_trd_le_snd_right
    (N : ModuleCat.{v} R) (S : ShortComplex (ModuleCat.{v} R)) (hS : S.ShortExact) :
    N.depth S.X₁ ⊓ N.depth S.X₃ ≤ N.depth S.X₂ := by
  have key : ∀ (M : ModuleCat.{v} R) (i : ℕ), (i : ℕ∞) < N.depth M →
      Subsingleton (Ext N M i) := by
    intro M i hi
    by_cases h : N.depth M = ⊤
    · exact (N.depth_eq_top_iff M).1 h i
    · obtain ⟨m, hm⟩ := ENat.ne_top_iff_exists.1 h
      rw [← hm] at hi
      exact ((N.depth_eq_iff M m).1 hm.symm).2 i (by exact_mod_cast hi)
  by_cases h2 : N.depth S.X₂ = ⊤
  · rw [h2]; exact le_top
  obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.1 h2
  have hnt := ((N.depth_eq_iff S.X₂ n).1 hn.symm).1
  by_contra hlt
  rw [not_le, ← hn, lt_inf_iff] at hlt
  have h1 := key S.X₁ n hlt.1
  have h3 := key S.X₃ n hlt.2
  obtain ⟨x, y, hxy⟩ := hnt
  apply hxy
  have hz : ∀ z : Ext N S.X₂ n, z = 0 := by
    intro z
    obtain ⟨x₁, hx₁⟩ := Ext.covariant_sequence_exact₂ (X := N) (hS := hS) (x₂ := z)
      (hx₂ := Subsingleton.elim _ _)
    rw [← hx₁, Subsingleton.elim x₁ 0, Ext.zero_comp]
  rw [hz x, hz y]
