/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     Real.hasDerivAt_Gamma_of_pos
Source:      Mathlib @ a02a63c2, Mathlib/Analysis/SpecialFunctions/Gamma/Deriv.lean, line 155
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  O2-repair-vs-resample, arm B, verified in round 1 (round 0 = first attempt)
Prover:      claude-opus-5-5
Setup:       Opus 5.5: arm B = one attempt plus up to 3 repair rounds with Lean error messages; arm A = 4 independent attempts (attempt k)
Check:       the proof replaced the human proof in the Mathlib file above; Lean reported
             0 errors and no `sorry`; sorry/admit/native_decide/search tactics were rejected.
-/

-- (context: the Mathlib file above this declaration)
theorem hasDerivAt_Gamma_of_pos {s : ℝ} (hs : 0 < s) :
    HasDerivAt Gamma (∫ t in Ioi 0, t ^ (s - 1) * (log t * exp (-t))) s := by
  have h := (Complex.hasDerivAt_Gamma_of_re_pos (s := (s : ℂ)) (by simpa using hs)).real_of_complex
  have h1 : (fun x : ℝ => (Complex.Gamma (x : ℂ)).re) = Real.Gamma := by
    ext x
    rw [Complex.Gamma_ofReal, ofReal_re]
  have h2 : (∫ t : ℝ in Ioi 0, (t : ℂ) ^ ((s : ℂ) - 1) *
      ((Real.log t : ℂ) * (Real.exp (-t) : ℂ))) =
      ((∫ t in Ioi 0, t ^ (s - 1) * (Real.log t * Real.exp (-t)) : ℝ) : ℂ) := by
    rw [← integral_complex_ofReal]
    refine setIntegral_congr_fun measurableSet_Ioi (fun t ht => ?_)
    simp only [ofReal_mul, ofReal_cpow (mem_Ioi.mp ht).le, ofReal_sub, ofReal_one]
  rw [h1, h2, ofReal_re] at h
  exact h
