/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     MeasureTheory.MemLp.add_measure
Source:      Mathlib @ a02a63c2, Mathlib/MeasureTheory/Function/LpSeminorm/Basic.lean, line 984
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  O2-repair-vs-resample, arm B, verified in round 0 (round 0 = first attempt)
Prover:      claude-opus-5-5
Setup:       Opus 5.5: arm B = one attempt plus up to 3 repair rounds with Lean error messages; arm A = 4 independent attempts (attempt k)
Check:       the proof replaced the human proof in the Mathlib file above; Lean reported
             0 errors and no `sorry`; sorry/admit/native_decide/search tactics were rejected.
-/

-- (context: the Mathlib file above this declaration)
lemma MemLp.add_measure (h1 : MemLp f p μ) (h2 : MemLp f p ν) : MemLp f p (μ + ν) := by
  have hm : AEStronglyMeasurable f (μ + ν) :=
    h1.aestronglyMeasurable.add_measure h2.aestronglyMeasurable
  by_cases hp0 : p = 0
  · subst hp0
    exact memLp_zero_iff_aestronglyMeasurable.2 hm
  by_cases hpt : p = ∞
  · subst hpt
    show eLpNorm f ∞ (μ + ν) < ∞
    rw [eLpNorm_exponent_top hm, eLpNormEssSup_add_measure]
    have a := h1.eLpNorm_lt_top
    have b := h2.eLpNorm_lt_top
    rw [eLpNorm_exponent_top h1.aestronglyMeasurable] at a
    rw [eLpNorm_exponent_top h2.aestronglyMeasurable] at b
    exact max_lt a b
  · show eLpNorm f p (μ + ν) < ∞
    rw [eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top hp0 hpt hm, lintegral_add_measure]
    exact ENNReal.add_lt_top.2
      ⟨(eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top hp0 hpt
          h1.aestronglyMeasurable).1 h1.eLpNorm_lt_top,
        (eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top hp0 hpt
          h2.aestronglyMeasurable).1 h2.eLpNorm_lt_top⟩
