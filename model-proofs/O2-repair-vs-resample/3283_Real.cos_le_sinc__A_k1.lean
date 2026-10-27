/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     Real.cos_le_sinc
Source:      Mathlib @ a02a63c2, Mathlib/Analysis/SpecialFunctions/Trigonometric/Sinc.lean, line 100
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  O2-repair-vs-resample, arm A, attempt 1, verified in round 0 (round 0 = first attempt)
Prover:      claude-opus-5-5
Setup:       Opus 5.5: arm B = one attempt plus up to 3 repair rounds with Lean error messages; arm A = 4 independent attempts (attempt k)
Check:       the proof replaced the human proof in the Mathlib file above; Lean reported
             0 errors and no `sorry`; sorry/admit/native_decide/search tactics were rejected.
-/

-- (context: the Mathlib file above this declaration)
lemma cos_le_sinc (hx : |x| < π / 2) : cos x ≤ sinc x := by
  obtain ⟨h1, h2⟩ := abs_lt.mp hx
  have key : ∀ y : ℝ, 0 < y → y < π / 2 → cos y ≤ sinc y := by
    intro y hy hy2
    have hc : 0 < cos y := cos_pos_of_mem_Ioo ⟨by linarith, hy2⟩
    rw [sinc_of_ne_zero hy.ne', le_div_iff₀ hy, ← tan_mul_cos hc.ne']
    nlinarith [lt_tan hy hy2]
  rcases lt_trichotomy x 0 with h | rfl | h
  · have := key (-x) (by linarith) (by linarith)
    simpa using this
  · simp
  · exact key x h h2
