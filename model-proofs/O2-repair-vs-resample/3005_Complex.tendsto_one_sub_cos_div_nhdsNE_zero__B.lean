/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     Complex.tendsto_one_sub_cos_div_nhdsNE_zero
Source:      Mathlib @ a02a63c2, Mathlib/Analysis/SpecialFunctions/Trigonometric/Deriv.lean, line 140
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  O2-repair-vs-resample, arm B, verified in round 0 (round 0 = first attempt)
Prover:      claude-opus-5-5
Setup:       Opus 5.5: arm B = one attempt plus up to 3 repair rounds with Lean error messages; arm A = 4 independent attempts (attempt k)
Check:       the proof replaced the human proof in the Mathlib file above; Lean reported
             0 errors and no `sorry`; sorry/admit/native_decide/search tactics were rejected.
-/

-- (context: the Mathlib file above this declaration)
theorem tendsto_one_sub_cos_div_nhdsNE_zero :
    Filter.Tendsto (fun z : ℂ ↦ (1 - cos z) / z) (𝓝[≠] 0) (𝓝 0) := by
  have h : HasDerivAt cos 0 0 := by simpa using hasDerivAt_cos 0
  have h2 := (hasDerivAt_iff_tendsto_slope.mp h).neg
  simp only [neg_zero] at h2
  refine h2.congr fun z ↦ ?_
  simp only [slope_def_field, cos_zero, sub_zero]
  ring
