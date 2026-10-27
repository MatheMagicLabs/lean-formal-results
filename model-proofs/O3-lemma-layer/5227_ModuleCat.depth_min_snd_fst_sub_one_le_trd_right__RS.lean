/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     ModuleCat.depth_min_snd_fst_sub_one_le_trd_right
Source:      Mathlib @ a02a63c2, Mathlib/RingTheory/Depth/Basic.lean, line 300
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  O3-lemma-layer, arm RS, verified in round 0 (round 0 = first attempt)
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
  have key : ∀ (i : ℕ) (a : ℕ∞), (i : ℕ∞) < a - 1 → ((i + 1 : ℕ) : ℕ∞) < a := by
    intro i a ha
    induction a using ENat.recTopCoe with
    | top => exact ENat.coe_lt_top _
    | coe m =>
      rw [← ENat.coe_one, ← ENat.coe_sub, Nat.cast_lt] at ha
      exact Nat.cast_lt.mpr (by omega)
  unfold ModuleCat.depth
  apply le_sSup
  intro i hi
  rcases lt_inf_iff.mp hi with ⟨h2, h1⟩
  obtain ⟨n2, hn2, hi2⟩ := lt_sSup_iff.mp h2
  have h1' := key i _ h1
  obtain ⟨n1, hn1, hi1⟩ := lt_sSup_iff.mp h1'
  haveI s2 := hn2 i hi2
  haveI s1 := hn1 (i + 1) hi1
  refine subsingleton_of_forall_eq 0 (fun x => ?_)
  obtain ⟨x₂, hx₂⟩ := Ext.covariant_sequence_exact₃ (X := N) (hS := hS) x rfl
    (Subsingleton.elim _ _)
  rw [← hx₂, Subsingleton.elim x₂ 0, Ext.zero_comp]
