/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     MeasureTheory.eLpNorm_const_mul_ennreal
Source:      Mathlib @ a02a63c2, Mathlib/MeasureTheory/Function/LpSeminorm/SMul.lean, line 157
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  O5-repair-sonnet, arm B, verified in round 2 (round 0 = first attempt)
Prover:      claude-sonnet-5-5
Setup:       Sonnet 5.5: arm B = repair loop; arm A = independent attempts
Check:       the proof replaced the human proof in the Mathlib file above; Lean reported
             0 errors and no `sorry`; sorry/admit/native_decide/search tactics were rejected.
-/

-- (context: the Mathlib file above this declaration)
theorem eLpNorm_const_mul_ennreal {f : α → ℝ≥0∞} {c : ℝ≥0∞} (hf : AEStronglyMeasurable f μ) :
    eLpNorm (fun x ↦ c * f x) p μ = c * eLpNorm f p μ := by
  have hg : AEStronglyMeasurable (fun x ↦ c * f x) μ :=
    (hf.aemeasurable.const_mul c).aestronglyMeasurable
  by_cases hp0 : p = 0
  · simp [eLpNorm, hp0, hf, hg]
  by_cases hp : p = ∞
  · subst hp
    simp [eLpNorm, hf, hg, eLpNormEssSup_eq_essSup_enorm]
    try exact ENNReal.essSup_const_mul
  · rw [eLpNorm_eq_eLpNorm' hp0 hp, eLpNorm_eq_eLpNorm' hp0 hp]
    all_goals first
      | exact eLpNorm'_const_mul_ennreal (ENNReal.toReal_pos hp0 hp) hf
      | exact hf
      | exact hg
