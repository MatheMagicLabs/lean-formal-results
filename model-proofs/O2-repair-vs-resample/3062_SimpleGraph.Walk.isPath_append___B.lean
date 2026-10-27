/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     SimpleGraph.Walk.isPath_append'
Source:      Mathlib @ a02a63c2, Mathlib/Combinatorics/SimpleGraph/Paths.lean, line 178
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  O2-repair-vs-resample, arm B, verified in round 2 (round 0 = first attempt)
Prover:      claude-opus-5-5
Setup:       Opus 5.5: arm B = one attempt plus up to 3 repair rounds with Lean error messages; arm A = 4 independent attempts (attempt k)
Check:       the proof replaced the human proof in the Mathlib file above; Lean reported
             0 errors and no `sorry`; sorry/admit/native_decide/search tactics were rejected.
-/

-- (context: the Mathlib file above this declaration)
theorem isPath_append' (p : G.Walk u v) (q : G.Walk v w) :
    (p.append q).IsPath ↔ p.dropLast.IsPath ∧ q.IsPath ∧ p.support.dropLast.Disjoint q.support := by
  by_cases hp : p.Nil
  · cases p with
    | nil => simp [isPath_def]
    | cons h p => simp at hp
  · obtain ⟨w', r, h, rfl⟩ : ∃ (w' : V) (r : G.Walk u w') (h : G.Adj w' v), p = r.concat h := by
      exact ⟨_, _, _, (concat_dropLast (p.adj_penultimate hp)).symm⟩
    simp only [isPath_def, concat_append, support_append, support_cons, List.tail_cons,
      support_concat, List.concat_eq_append, List.dropLast_concat]
    first
      | simp only [dropLast_concat, support_copy]
      | skip
    rw [List.nodup_append']
