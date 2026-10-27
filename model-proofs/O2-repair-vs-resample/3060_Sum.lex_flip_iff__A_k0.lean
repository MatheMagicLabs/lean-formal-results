/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     Sum.lex_flip_iff
Source:      Mathlib @ a02a63c2, Mathlib/Order/Sum/Order.lean, line 105
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  O2-repair-vs-resample, arm A, attempt 0, verified in round 0 (round 0 = first attempt)
Prover:      claude-opus-5-5
Setup:       Opus 5.5: arm B = one attempt plus up to 3 repair rounds with Lean error messages; arm A = 4 independent attempts (attempt k)
Check:       the proof replaced the human proof in the Mathlib file above; Lean reported
             0 errors and no `sorry`; sorry/admit/native_decide/search tactics were rejected.
-/

-- (context: the Mathlib file above this declaration)
theorem lex_flip_iff (a b : α ⊕ β) : Lex (flip r) (flip s) a b ↔ Lex s r b.swap a.swap := by
  cases a <;> cases b <;> simp [flip, Lex.sep]
