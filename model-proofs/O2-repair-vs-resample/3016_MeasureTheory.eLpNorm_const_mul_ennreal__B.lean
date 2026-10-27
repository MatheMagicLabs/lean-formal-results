/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     MeasureTheory.eLpNorm_const_mul_ennreal
Source:      Mathlib @ a02a63c2, Mathlib/MeasureTheory/Function/LpSeminorm/SMul.lean, line 157
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  O2-repair-vs-resample, arm B, verified in round 1 (round 0 = first attempt)
Prover:      claude-opus-5-5
Setup:       Opus 5.5: arm B = one attempt plus up to 3 repair rounds with Lean error messages; arm A = 4 independent attempts (attempt k)
Check:       the proof replaced the human proof in the Mathlib file above; Lean reported
             0 errors and no `sorry`; sorry/admit/native_decide/search tactics were rejected.
-/

-- (context: the Mathlib file above this declaration)
theorem eLpNorm_const_mul_ennreal {f : α → ℝ≥0∞} {c : ℝ≥0∞} (hf : AEStronglyMeasurable f μ) :
    eLpNorm (fun x ↦ c * f x) p μ = c * eLpNorm f p μ := by
  have hg : AEStronglyMeasurable (fun x ↦ c * f x) μ :=
    (hf.aemeasurable.const_mul c).aestronglyMeasurable
  rcases eq_or_ne p 0 with rfl | hp0
  · simp [eLpNorm, hf, hg]
  rcases eq_or_ne p ∞ with rfl | hptop
  · simp [eLpNorm, hf, hg, eLpNormEssSup_eq_essSup_enorm, ENNReal.essSup_const_mul]
  · rw [eLpNorm_eq_eLpNorm' hp0 hptop, eLpNorm_eq_eLpNorm' hp0 hptop]
    · exact eLpNorm'_const_mul_ennreal (ENNReal.toReal_pos hp0 hptop) hf
    all_goals first | exact hf | exact hg
