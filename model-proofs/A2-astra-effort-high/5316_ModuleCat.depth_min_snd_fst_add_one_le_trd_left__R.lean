/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     ModuleCat.depth_min_snd_fst_add_one_le_trd_left
Source:      Mathlib @ a02a63c2, Mathlib/RingTheory/Depth/Basic.lean, line 245
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  A2-astra-effort-high, arm R, verified in round 1 (round 0 = first attempt)
Prover:      gpt-6-astra
Setup:       GPT-6 Astra, reasoning effort high (arms R, N0)
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
  apply le_sSup
  simp only [Set.mem_ofPred_eq, lt_inf_iff, and_imp]
  intro i hi2 hi1
  have zero2 := AddCommGrpCat.isZero_of_iff_subsingleton.mpr
    (subsingleton_ext_of_lt_depth hi2)
  match i with
  | 0 =>
    simp only [AddCommGrpCat.isZero_iff_subsingleton] at zero2 ⊢
    exact (Ext.precomp_mk₀_injective_of_epi N S.g (hg := hS.epi_g)).subsingleton
  | i + 1 =>
    have hi1' : i < S.X₁.depth N := by simpa using hi1
    have zero1 : IsZero (AddCommGrpCat.of (Ext S.X₁ N i)) :=
      AddCommGrpCat.isZero_of_iff_subsingleton.mpr
        (subsingleton_ext_of_lt_depth hi1')
    exact AddCommGrpCat.subsingleton_of_isZero <|
      ShortComplex.Exact.isZero_of_both_zeros
        (Ext.contravariant_sequence_exact₃' hS N i (i + 1) (by omega))
        (zero1.eq_zero_of_src _) (zero2.eq_zero_of_tgt _)
