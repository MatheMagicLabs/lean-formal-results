/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     ZFSet.choice_cmem
Source:      Mathlib @ a02a63c2, Mathlib/SetTheory/ZFC/Class.lean, line 534
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  O2-repair-vs-resample, arm B, verified in round 0 (round 0 = first attempt)
Prover:      claude-opus-5-5
Setup:       Opus 5.5: arm B = one attempt plus up to 3 repair rounds with Lean error messages; arm A = 4 independent attempts (attempt k)
Check:       the proof replaced the human proof in the Mathlib file above; Lean reported
             0 errors and no `sorry`; sorry/admit/native_decide/search tactics were rejected.
-/

-- (context: the Mathlib file above this declaration)
theorem choice_cmem (h : ∅ ∉ x) (y : ZFSet.{u}) (yx : y ∈ x) : choice x ′ y ᶜ∈ y := by
  delta choice
  rw [@map_fval _ _ _ (Classical.allZFSetDefinable _) yx]
  exact ZFClass.coe_cmem.2 (choice_mem_aux x h y yx)
