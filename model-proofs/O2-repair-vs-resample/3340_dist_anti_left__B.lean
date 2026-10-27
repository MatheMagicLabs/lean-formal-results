/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     dist_anti_left
Source:      Mathlib @ a02a63c2, Mathlib/Analysis/Normed/Order/UpperLower.lean, line 131
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  O2-repair-vs-resample, arm B, verified in round 0 (round 0 = first attempt)
Prover:      claude-opus-5-5
Setup:       Opus 5.5: arm B = one attempt plus up to 3 repair rounds with Lean error messages; arm A = 4 independent attempts (attempt k)
Check:       the proof replaced the human proof in the Mathlib file above; Lean reported
             0 errors and no `sorry`; sorry/admit/native_decide/search tactics were rejected.
-/

-- (context: the Mathlib file above this declaration)
lemma dist_anti_left {y : α} : AntitoneOn (dist · y) (Iic y) := by
  intro y₁ hy₁ y₂ hy₂ hy
  simp only [dist_eq_norm]
  apply norm_le_norm_of_abs_le_abs
  rw [abs_of_nonpos (sub_nonpos.mpr hy₂), abs_of_nonpos (sub_nonpos.mpr hy₁)]
  exact neg_le_neg (sub_le_sub_right hy y)
