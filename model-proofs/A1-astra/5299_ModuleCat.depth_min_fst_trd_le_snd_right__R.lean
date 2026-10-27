/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     ModuleCat.depth_min_fst_trd_le_snd_right
Source:      Mathlib @ a02a63c2, Mathlib/RingTheory/Depth/Basic.lean, line 264
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

@[stacks 00LX "(1)"]
lemma depth_min_fst_trd_le_snd_right
    (N : ModuleCat.{v} R) (S : ShortComplex (ModuleCat.{v} R)) (hS : S.ShortExact) :
    N.depth S.X₁ ⊓ N.depth S.X₃ ≤ N.depth S.X₂ := by
  set_option maxHeartbeats 0 in
    change _ ≤ sSup {n : ℕ∞ | ∀ i : ℕ, ↑i < n → Subsingleton (Ext N S.X₂ i)}
    refine le_sSup ?_
    intro i hi
    have h₁ : Subsingleton (Ext N S.X₁ i) :=
      subsingleton_ext_of_lt_depth (lt_of_lt_of_le hi inf_le_left)
    have h₃ : Subsingleton (Ext N S.X₃ i) :=
      subsingleton_ext_of_lt_depth (lt_of_lt_of_le hi inf_le_right)
    have z₁ : IsZero (AddCommGrpCat.of (Ext N S.X₁ i)) :=
      AddCommGrpCat.isZero_of_iff_subsingleton.mpr h₁
    have z₃ : IsZero (AddCommGrpCat.of (Ext N S.X₃ i)) :=
      AddCommGrpCat.isZero_of_iff_subsingleton.mpr h₃
    exact AddCommGrpCat.subsingleton_of_isZero
      (ShortComplex.Exact.isZero_of_both_zeros
        (Ext.covariant_sequence_exact₂' N hS i)
        (z₁.eq_zero_of_src _) (z₃.eq_zero_of_tgt _))
