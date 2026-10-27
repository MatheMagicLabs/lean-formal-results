/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     Real.tendsto_one_sub_cos_div_nhdsNE_zero
Source:      Mathlib @ a02a63c2, Mathlib/Analysis/SpecialFunctions/Trigonometric/Deriv.lean, line 417
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  O2-repair-vs-resample, arm A, attempt 1, verified in round 0 (round 0 = first attempt)
Prover:      claude-opus-5-5
Setup:       Opus 5.5: arm B = one attempt plus up to 3 repair rounds with Lean error messages; arm A = 4 independent attempts (attempt k)
Check:       the proof replaced the human proof in the Mathlib file above; Lean reported
             0 errors and no `sorry`; sorry/admit/native_decide/search tactics were rejected.
-/

-- (context: the Mathlib file above this declaration)
theorem tendsto_one_sub_cos_div_nhdsNE_zero :
    Filter.Tendsto (fun x : ℝ ↦ (1 - cos x) / x) (𝓝[≠] 0) (𝓝 0) := by
  have hd : HasDerivAt cos 0 0 := by simpa using hasDerivAt_cos 0
  simpa [slope_def_field, ← neg_div, neg_sub] using (hasDerivAt_iff_tendsto_slope.mp hd).neg
