/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     MeasureTheory.MemLp.add_measure
Source:      Mathlib @ a02a63c2, Mathlib/MeasureTheory/Function/LpSeminorm/Basic.lean, line 984
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  O2-repair-vs-resample, arm A, attempt 0, verified in round 0 (round 0 = first attempt)
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
  by_cases hptop : p = ∞
  · subst hptop
    show eLpNorm f ∞ (μ + ν) < ∞
    have e1 := h1.eLpNorm_lt_top
    have e2 := h2.eLpNorm_lt_top
    rw [eLpNorm_exponent_top h1.aestronglyMeasurable] at e1
    rw [eLpNorm_exponent_top h2.aestronglyMeasurable] at e2
    rw [eLpNorm_exponent_top hm, eLpNormEssSup_add_measure]
    exact max_lt e1 e2
  show eLpNorm f p (μ + ν) < ∞
  rw [eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top hp0 hptop hm, lintegral_add_measure]
  exact ENNReal.add_lt_top.2
    ⟨lintegral_rpow_enorm_lt_top_of_eLpNorm_lt_top hp0 hptop h1.eLpNorm_lt_top,
     lintegral_rpow_enorm_lt_top_of_eLpNorm_lt_top hp0 hptop h2.eLpNorm_lt_top⟩
