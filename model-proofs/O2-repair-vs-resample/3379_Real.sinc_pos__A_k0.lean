/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     Real.sinc_pos
Source:      Mathlib @ a02a63c2, Mathlib/Analysis/SpecialFunctions/Trigonometric/Sinc.lean, line 110
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  O2-repair-vs-resample, arm A, attempt 0, verified in round 0 (round 0 = first attempt)
Prover:      claude-opus-5-5
Setup:       Opus 5.5: arm B = one attempt plus up to 3 repair rounds with Lean error messages; arm A = 4 independent attempts (attempt k)
Check:       the proof replaced the human proof in the Mathlib file above; Lean reported
             0 errors and no `sorry`; sorry/admit/native_decide/search tactics were rejected.
-/

-- (context: the Mathlib file above this declaration)
lemma sinc_pos (hx : |x| < π) : 0 < sinc x := by
  by_cases hx0 : x = 0
  · simp [hx0]
  rw [sinc_of_ne_zero hx0]
  have hb := abs_lt.mp hx
  rcases lt_or_gt_of_ne hx0 with h | h
  · have h1 := sin_pos_of_pos_of_lt_pi (neg_pos.mpr h) (by linarith [hb.1])
    rw [sin_neg] at h1
    exact div_pos_of_neg_of_neg (by linarith) h
  · exact div_pos (sin_pos_of_pos_of_lt_pi h hb.2) h
