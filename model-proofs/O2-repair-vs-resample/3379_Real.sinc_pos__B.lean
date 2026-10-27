/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     Real.sinc_pos
Source:      Mathlib @ a02a63c2, Mathlib/Analysis/SpecialFunctions/Trigonometric/Sinc.lean, line 110
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  O2-repair-vs-resample, arm B, verified in round 0 (round 0 = first attempt)
Prover:      claude-opus-5-5
Setup:       Opus 5.5: arm B = one attempt plus up to 3 repair rounds with Lean error messages; arm A = 4 independent attempts (attempt k)
Check:       the proof replaced the human proof in the Mathlib file above; Lean reported
             0 errors and no `sorry`; sorry/admit/native_decide/search tactics were rejected.
-/

-- (context: the Mathlib file above this declaration)
lemma sinc_pos (hx : |x| < π) : 0 < sinc x := by
  rcases lt_trichotomy x 0 with h | rfl | h
  · rw [sinc_of_ne_zero h.ne]
    have h1 : sin x < 0 := sin_neg_of_neg_of_neg_pi_lt h (abs_lt.mp hx).1
    exact div_pos_iff.mpr (Or.inr ⟨h1, h⟩)
  · simp
  · rw [sinc_of_ne_zero h.ne']
    exact div_pos (sin_pos_of_pos_of_lt_pi h (abs_lt.mp hx).2) h
