/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     ModuleCat.depth_min_snd_trd_sub_one_le_fst_left
Source:      Mathlib @ a02a63c2, Mathlib/RingTheory/Depth/Basic.lean, line 230
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

lemma depth_min_snd_trd_sub_one_le_fst_left
    (S : ShortComplex (ModuleCat.{v} R)) (hS : S.ShortExact) (N : ModuleCat.{v} R) :
    S.X₂.depth N ⊓ (S.X₃.depth N - 1) ≤ S.X₁.depth N := by
  unfold ModuleCat.depth
  apply le_sSup
  intro i hi
  have hi2 : (i : ℕ∞) < S.X₂.depth N := lt_of_lt_of_le hi inf_le_left
  have hi3 : ((i + 1 : ℕ) : ℕ∞) < S.X₃.depth N := by
    have h : (i : ℕ∞) < S.X₃.depth N - 1 := lt_of_lt_of_le hi inf_le_right
    generalize S.X₃.depth N = d at h ⊢
    induction d using ENat.recTopCoe with
    | top => exact ENat.coe_lt_top _
    | coe m =>
      have h' : ((i : ℕ) : ℕ∞) < ((m - 1 : ℕ) : ℕ∞) := by
        rw [ENat.coe_sub, Nat.cast_one]; exact h
      have := ENat.coe_lt_coe.mp h'
      exact ENat.coe_lt_coe.mpr (by omega)
  unfold ModuleCat.depth at hi2 hi3
  obtain ⟨n2, hn2, hin2⟩ := lt_sSup_iff.mp hi2
  obtain ⟨n3, hn3, hin3⟩ := lt_sSup_iff.mp hi3
  have s2 := hn2 i hin2
  have s3 := hn3 (i + 1) hin3
  have s3' : Subsingleton (Ext S.X₃ N (1 + i)) := by
    rw [Nat.add_comm]; exact s3
  constructor
  intro a b
  obtain ⟨ya, hya⟩ := Ext.contravariant_sequence_exact₁ hS N a rfl
    (Subsingleton.elim _ _)
  obtain ⟨yb, hyb⟩ := Ext.contravariant_sequence_exact₁ hS N b rfl
    (Subsingleton.elim _ _)
  rw [← hya, ← hyb, Subsingleton.elim ya yb]
