/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     ModuleCat.depth_min_fst_trd_le_snd_right
Source:      Mathlib @ a02a63c2, Mathlib/RingTheory/Depth/Basic.lean, line 264
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

@[stacks 00LX "(1)"]
lemma depth_min_fst_trd_le_snd_right
    (N : ModuleCat.{v} R) (S : ShortComplex (ModuleCat.{v} R)) (hS : S.ShortExact) :
    N.depth S.X₁ ⊓ N.depth S.X₃ ≤ N.depth S.X₂ := by
  unfold ModuleCat.depth
  apply le_sSup
  simp only [Set.mem_setOf_eq]
  intro i hi
  obtain ⟨n₁, hn₁, hi₁⟩ := lt_sSup_iff.mp (lt_of_lt_of_le hi inf_le_left)
  obtain ⟨n₃, hn₃, hi₃⟩ := lt_sSup_iff.mp (lt_of_lt_of_le hi inf_le_right)
  have h₁ := hn₁ i hi₁
  have h₃ := hn₃ i hi₃
  refine ⟨fun x y => ?_⟩
  obtain ⟨x₁, hx₁⟩ := Ext.covariant_sequence_exact₂ (X := N) (hS := hS) (x₂ := x)
    (hx₂ := Subsingleton.elim _ _)
  obtain ⟨y₁, hy₁⟩ := Ext.covariant_sequence_exact₂ (X := N) (hS := hS) (x₂ := y)
    (hx₂ := Subsingleton.elim _ _)
  rw [← hx₁, ← hy₁, Subsingleton.elim x₁ 0, Subsingleton.elim y₁ 0]
