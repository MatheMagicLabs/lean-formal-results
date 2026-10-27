/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     Filter.limsSup_pure
Source:      Mathlib @ a02a63c2, Mathlib/Order/LiminfLimsup.lean, line 61
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  O2-repair-vs-resample, arm A, attempt 2, verified in round 0 (round 0 = first attempt)
Prover:      claude-opus-5-5
Setup:       Opus 5.5: arm B = one attempt plus up to 3 repair rounds with Lean error messages; arm A = 4 independent attempts (attempt k)
Check:       the proof replaced the human proof in the Mathlib file above; Lean reported
             0 errors and no `sorry`; sorry/admit/native_decide/search tactics were rejected.
-/

-- (context: the Mathlib file above this declaration)
@[to_dual (attr := simp)]
lemma limsSup_pure (a : α) : limsSup (pure a) = a := by
  change sInf (Set.Ici a) = a
  exact csInf_Ici
