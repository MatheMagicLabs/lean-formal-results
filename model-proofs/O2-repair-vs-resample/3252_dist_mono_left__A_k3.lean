/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     dist_mono_left
Source:      Mathlib @ a02a63c2, Mathlib/Analysis/Normed/Order/UpperLower.lean, line 121
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  O2-repair-vs-resample, arm A, attempt 3, verified in round 0 (round 0 = first attempt)
Prover:      claude-opus-5-5
Setup:       Opus 5.5: arm B = one attempt plus up to 3 repair rounds with Lean error messages; arm A = 4 independent attempts (attempt k)
Check:       the proof replaced the human proof in the Mathlib file above; Lean reported
             0 errors and no `sorry`; sorry/admit/native_decide/search tactics were rejected.
-/

-- (context: the Mathlib file above this declaration)
lemma dist_mono_left {y : α} : MonotoneOn (dist · y) (Ici y) := by
  intro a ha b hb hab
  simp only [mem_Ici] at ha hb
  simp only [dist_eq_norm]
  apply norm_le_norm_of_abs_le_abs
  rw [abs_of_nonneg (sub_nonneg.2 ha), abs_of_nonneg (sub_nonneg.2 hb)]
  exact sub_le_sub_right hab y
