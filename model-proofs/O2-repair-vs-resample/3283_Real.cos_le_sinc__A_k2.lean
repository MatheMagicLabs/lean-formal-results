/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     Real.cos_le_sinc
Source:      Mathlib @ a02a63c2, Mathlib/Analysis/SpecialFunctions/Trigonometric/Sinc.lean, line 100
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  O2-repair-vs-resample, arm A, attempt 2, verified in round 0 (round 0 = first attempt)
Prover:      claude-opus-5-5
Setup:       Opus 5.5: arm B = one attempt plus up to 3 repair rounds with Lean error messages; arm A = 4 independent attempts (attempt k)
Check:       the proof replaced the human proof in the Mathlib file above; Lean reported
             0 errors and no `sorry`; sorry/admit/native_decide/search tactics were rejected.
-/

-- (context: the Mathlib file above this declaration)
lemma cos_le_sinc (hx : |x| < π / 2) : cos x ≤ sinc x := by
  have key : ∀ y : ℝ, 0 < y → y < π / 2 → cos y ≤ sinc y := by
    intro y hy0 hy1
    rw [sinc_of_ne_zero hy0.ne', le_div_iff₀ hy0]
    have hc : 0 < cos y := cos_pos_of_mem_Ioo ⟨by linarith [pi_pos], hy1⟩
    have ht := (lt_tan hy0 hy1).le
    have := mul_le_mul_of_nonneg_right ht hc.le
    rw [tan_mul_cos hc.ne'] at this
    linarith
  rcases lt_trichotomy x 0 with h | h | h
  · have := key (-x) (by linarith) (by rw [abs_of_neg h] at hx; linarith)
    simpa using this
  · simp [h]
  · exact key x h (by rw [abs_of_pos h] at hx; exact hx)
