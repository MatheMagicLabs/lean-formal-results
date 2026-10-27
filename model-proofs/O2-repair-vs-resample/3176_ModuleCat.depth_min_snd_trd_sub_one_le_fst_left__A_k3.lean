/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     ModuleCat.depth_min_snd_trd_sub_one_le_fst_left
Source:      Mathlib @ a02a63c2, Mathlib/RingTheory/Depth/Basic.lean, line 230
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  O2-repair-vs-resample, arm A, attempt 3, verified in round 0 (round 0 = first attempt)
Prover:      claude-opus-5-5
Setup:       Opus 5.5: arm B = one attempt plus up to 3 repair rounds with Lean error messages; arm A = 4 independent attempts (attempt k)
Check:       the proof replaced the human proof in the Mathlib file above; Lean reported
             0 errors and no `sorry`; sorry/admit/native_decide/search tactics were rejected.
-/

-- (context: the Mathlib file above this declaration)
lemma depth_min_snd_trd_sub_one_le_fst_left
    (S : ShortComplex (ModuleCat.{v} R)) (hS : S.ShortExact) (N : ModuleCat.{v} R) :
    S.X₂.depth N ⊓ (S.X₃.depth N - 1) ≤ S.X₁.depth N := by
  apply le_sSup
  simp only [Set.mem_ofPred_eq, lt_inf_iff, and_imp]
  intro i hi2 hi3
  have h3 : ((i + 1 : ℕ) : ℕ∞) < S.X₃.depth N := by
    generalize S.X₃.depth N = d at hi3 ⊢
    induction d with
    | top => exact ENat.coe_lt_top _
    | coe d =>
      rw [← ENat.coe_one, ← ENat.coe_sub, ENat.coe_lt_coe] at hi3
      exact_mod_cast (by omega : i + 1 < d)
  have zero2 : IsZero (AddCommGrpCat.of (Ext S.X₂ N i)) :=
    AddCommGrpCat.isZero_of_iff_subsingleton.mpr (subsingleton_ext_of_lt_depth hi2)
  have zero3 : IsZero (AddCommGrpCat.of (Ext S.X₃ N (i + 1))) :=
    AddCommGrpCat.isZero_of_iff_subsingleton.mpr (subsingleton_ext_of_lt_depth h3)
  exact AddCommGrpCat.subsingleton_of_isZero <| ShortComplex.Exact.isZero_of_both_zeros
    (Ext.contravariant_sequence_exact₁' hS N i (i + 1) (by omega))
    (zero2.eq_zero_of_src _) (zero3.eq_zero_of_tgt _)
