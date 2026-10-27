/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     ModuleCat.depth_min_fst_trd_le_snd_right
Source:      Mathlib @ a02a63c2, Mathlib/RingTheory/Depth/Basic.lean, line 264
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  O2-repair-vs-resample, arm A, attempt 2, verified in round 0 (round 0 = first attempt)
Prover:      claude-opus-5-5
Setup:       Opus 5.5: arm B = one attempt plus up to 3 repair rounds with Lean error messages; arm A = 4 independent attempts (attempt k)
Check:       the proof replaced the human proof in the Mathlib file above; Lean reported
             0 errors and no `sorry`; sorry/admit/native_decide/search tactics were rejected.
-/

-- (context: the Mathlib file above this declaration)
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
