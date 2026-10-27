/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     continuous_const_cpow'
Source:      Mathlib @ a02a63c2, Mathlib/Analysis/SpecialFunctions/Pow/Continuity.lean, line 133
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  O2-repair-vs-resample, arm A, attempt 1, verified in round 0 (round 0 = first attempt)
Prover:      claude-opus-5-5
Setup:       Opus 5.5: arm B = one attempt plus up to 3 repair rounds with Lean error messages; arm A = 4 independent attempts (attempt k)
Check:       the proof replaced the human proof in the Mathlib file above; Lean reported
             0 errors and no `sorry`; sorry/admit/native_decide/search tactics were rejected.
-/

-- (context: the Mathlib file above this declaration)
@[fun_prop]
theorem continuous_const_cpow' {a : ℂ} (ha : a ≠ 0) : Continuous (fun x : ℂ => a ^ x) := by
  exact continuous_iff_continuousAt.2 fun _ => continuousAt_const_cpow ha
