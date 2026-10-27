/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     SimpleGraph.Walk.isPath_append
Source:      Mathlib @ a02a63c2, Mathlib/Combinatorics/SimpleGraph/Paths.lean, line 172
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  O2-repair-vs-resample, arm B, verified in round 0 (round 0 = first attempt)
Prover:      claude-opus-5-5
Setup:       Opus 5.5: arm B = one attempt plus up to 3 repair rounds with Lean error messages; arm A = 4 independent attempts (attempt k)
Check:       the proof replaced the human proof in the Mathlib file above; Lean reported
             0 errors and no `sorry`; sorry/admit/native_decide/search tactics were rejected.
-/

-- (context: the Mathlib file above this declaration)
theorem isPath_append (p : G.Walk u v) (q : G.Walk v w) :
    (p.append q).IsPath ↔ p.IsPath ∧ q.tail.IsPath ∧ p.support.Disjoint q.support.tail := by
  cases q with
  | nil =>
    simp only [append_nil, support_nil, List.tail_cons, List.disjoint_nil_right, and_true]
    constructor
    · intro h
      exact ⟨h, by first | simp [isPath_def] | exact IsPath.nil⟩
    · exact fun h => h.1
  | cons h q =>
    simp [isPath_def, support_append, support_cons, List.tail_cons, List.nodup_append']
