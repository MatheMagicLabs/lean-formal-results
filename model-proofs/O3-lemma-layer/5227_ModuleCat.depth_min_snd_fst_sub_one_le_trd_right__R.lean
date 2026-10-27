/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     ModuleCat.depth_min_snd_fst_sub_one_le_trd_right
Source:      Mathlib @ a02a63c2, Mathlib/RingTheory/Depth/Basic.lean, line 300
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  O3-lemma-layer, arm R, verified in round 0 (round 0 = first attempt)
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

@[stacks 00LX "(2)"]
lemma depth_min_snd_fst_sub_one_le_trd_right
    (N : ModuleCat.{v} R) (S : ShortComplex (ModuleCat.{v} R)) (hS : S.ShortExact) :
    N.depth S.X₂ ⊓ (N.depth S.X₁ - 1) ≤ N.depth S.X₃ := by
  classical
  unfold ModuleCat.depth
  apply le_sSup
  intro i hi
  obtain ⟨h2, h1⟩ := lt_inf_iff.mp hi
  have key : ∀ (a : ℕ∞) (j : ℕ), (j : ℕ∞) < a - 1 → ((j + 1 : ℕ) : ℕ∞) < a := by
    intro a j h
    induction a using ENat.recTopCoe with
    | top => exact ENat.coe_lt_top _
    | coe m =>
      have : j < m - 1 := by exact_mod_cast h
      exact_mod_cast (by omega : j + 1 < m)
  obtain ⟨n, hn, hin⟩ := lt_sSup_iff.mp h2
  have s2 := hn i hin
  obtain ⟨n', hn', hin'⟩ := lt_sSup_iff.mp (key _ _ h1)
  have s1 := hn' (i + 1) hin'
  rw [subsingleton_iff_forall_eq 0]
  intro z
  obtain ⟨x₂, hx₂⟩ := Ext.covariant_sequence_exact₃ N hS z rfl
    (@Subsingleton.elim _ s1 _ _)
  rw [← hx₂, @Subsingleton.elim _ s2 x₂ 0]
  simp
