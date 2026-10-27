/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     ModuleCat.depth_min_snd_trd_add_one_le_fst_right
Source:      Mathlib @ a02a63c2, Mathlib/RingTheory/Depth/Basic.lean, line 279
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  O2-repair-vs-resample, arm B, verified in round 0 (round 0 = first attempt)
Prover:      claude-opus-5-5
Setup:       Opus 5.5: arm B = one attempt plus up to 3 repair rounds with Lean error messages; arm A = 4 independent attempts (attempt k)
Check:       the proof replaced the human proof in the Mathlib file above; Lean reported
             0 errors and no `sorry`; sorry/admit/native_decide/search tactics were rejected.
-/

-- (context: the Mathlib file above this declaration)
@[stacks 00LX "(3)"]
lemma depth_min_snd_trd_add_one_le_fst_right
    (N : ModuleCat.{v} R) (S : ShortComplex (ModuleCat.{v} R)) (hS : S.ShortExact) :
    N.depth S.X₂ ⊓ (N.depth S.X₃ + 1) ≤ N.depth S.X₁ := by
  apply le_sSup
  simp only [Set.mem_ofPred_eq, lt_inf_iff, and_imp]
  intro i hi2 hi3
  have zero2 := AddCommGrpCat.isZero_of_iff_subsingleton.mpr (subsingleton_ext_of_lt_depth hi2)
  match i with
  | 0 =>
    simp only [AddCommGrpCat.isZero_iff_subsingleton] at zero2 ⊢
    first
    | exact (Ext.postcomp_mk₀_injective_of_mono N S.f (hf := hS.mono_f)).subsingleton
    | haveI := hS.mono_f
      haveI : Subsingleton (N ⟶ S.X₂) := Ext.addEquiv₀.symm.subsingleton
      haveI : Subsingleton (N ⟶ S.X₁) :=
        ⟨fun a b => (cancel_mono S.f).mp (Subsingleton.elim _ _)⟩
      exact Ext.addEquiv₀.subsingleton
  | i + 1 =>
    have hi3' : i < N.depth S.X₃ := by simpa using hi3
    have zero3 : IsZero (AddCommGrpCat.of (Ext N S.X₃ i)) :=
      AddCommGrpCat.isZero_of_iff_subsingleton.mpr (subsingleton_ext_of_lt_depth hi3')
    exact AddCommGrpCat.subsingleton_of_isZero <| ShortComplex.Exact.isZero_of_both_zeros
      (Ext.covariant_sequence_exact₁' N hS i (i + 1) (by omega))
      (zero3.eq_zero_of_src _) (zero2.eq_zero_of_tgt _)
