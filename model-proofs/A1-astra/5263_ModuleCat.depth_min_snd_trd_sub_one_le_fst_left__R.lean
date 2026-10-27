/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     ModuleCat.depth_min_snd_trd_sub_one_le_fst_left
Source:      Mathlib @ a02a63c2, Mathlib/RingTheory/Depth/Basic.lean, line 230
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  A1-astra, arm R, verified in round 3 (round 0 = first attempt)
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

lemma depth_min_snd_trd_sub_one_le_fst_left
    (S : ShortComplex (ModuleCat.{v} R)) (hS : S.ShortExact) (N : ModuleCat.{v} R) :
    S.X₂.depth N ⊓ (S.X₃.depth N - 1) ≤ S.X₁.depth N := by
  set_option maxHeartbeats 0 in
  set_option synthInstance.maxHeartbeats 0 in
    apply le_sSup
    simp only [Set.mem_ofPred_eq, lt_inf_iff, and_imp]
    intro i hi2 hi3
    have hi3' : (i + 1 : ℕ) < depth S.X₃ N := by
      simpa using lt_tsub_iff_right.mp hi3
    have zero2 : IsZero (AddCommGrpCat.of (Ext S.X₂ N i)) :=
      AddCommGrpCat.isZero_of_iff_subsingleton.mpr
        (subsingleton_ext_of_lt_depth hi2)
    have zero3 : IsZero (AddCommGrpCat.of (Ext S.X₃ N (i + 1))) :=
      AddCommGrpCat.isZero_of_iff_subsingleton.mpr
        (subsingleton_ext_of_lt_depth hi3')
    exact AddCommGrpCat.subsingleton_of_isZero <|
      ShortComplex.Exact.isZero_of_both_zeros
        (Ext.contravariant_sequence_exact₁' hS N i (i + 1) (add_comm _ _))
        (zero2.eq_zero_of_src _) (zero3.eq_zero_of_tgt _)
