/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     dist_mono_left
Source:      Mathlib @ a02a63c2, Mathlib/Analysis/Normed/Order/UpperLower.lean, line 121
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  O5-repair-sonnet, arm A, attempt 1, verified in round 0 (round 0 = first attempt)
Prover:      claude-sonnet-5-5
Setup:       Sonnet 5.5: arm B = repair loop; arm A = independent attempts
Check:       the proof replaced the human proof in the Mathlib file above; Lean reported
             0 errors and no `sorry`; sorry/admit/native_decide/search tactics were rejected.
-/

-- (context: the Mathlib file above this declaration)
lemma dist_mono_left {y : α} : MonotoneOn (dist · y) (Ici y) := by
  intro a ha b hb hab
  simp only [dist_eq_norm]
  apply HasSolidNorm.solid
  rw [abs_of_nonneg (sub_nonneg.2 ha), abs_of_nonneg (sub_nonneg.2 hb)]
  exact sub_le_sub_right hab y
