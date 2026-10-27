/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     ModuleCat.depth_min_fst_trd_le_snd_right
Source:      Mathlib @ a02a63c2, Mathlib/RingTheory/Depth/Basic.lean, line 264
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  LS1-leanstral-loop, arm L3, verified in round 1 (round 0 = first attempt)
Prover:      labs-leanstral-1-5
Setup:       Leanstral 1.5 in a fixed check-and-repair loop: L1 = 1 candidate per round, L3 = up to 3
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
  apply le_sSup
  simp only [Set.mem_ofPred_eq, lt_inf_iff, and_imp]
  intro i hi1 hi3
  have zero1 : IsZero (AddCommGrpCat.of (Ext N S.X₁ i)) :=
    AddCommGrpCat.isZero_of_iff_subsingleton.mpr (subsingleton_ext_of_lt_depth hi1)
  have zero3 : IsZero (AddCommGrpCat.of (Ext N S.X₃ i)) :=
    AddCommGrpCat.isZero_of_iff_subsingleton.mpr (subsingleton_ext_of_lt_depth hi3)
  exact AddCommGrpCat.subsingleton_of_isZero <| ShortComplex.Exact.isZero_of_both_zeros
    (Ext.covariant_sequence_exact₂' N hS i)
    (zero1.eq_zero_of_src _) (zero3.eq_zero_of_tgt _)
