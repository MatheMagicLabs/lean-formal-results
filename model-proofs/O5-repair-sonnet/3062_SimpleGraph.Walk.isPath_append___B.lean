/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     SimpleGraph.Walk.isPath_append'
Source:      Mathlib @ a02a63c2, Mathlib/Combinatorics/SimpleGraph/Paths.lean, line 178
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  O5-repair-sonnet, arm B, verified in round 3 (round 0 = first attempt)
Prover:      claude-sonnet-5-5
Setup:       Sonnet 5.5: arm B = repair loop; arm A = independent attempts
Check:       the proof replaced the human proof in the Mathlib file above; Lean reported
             0 errors and no `sorry`; sorry/admit/native_decide/search tactics were rejected.
-/

-- (context: the Mathlib file above this declaration)
theorem isPath_append' (p : G.Walk u v) (q : G.Walk v w) :
    (p.append q).IsPath ↔ p.dropLast.IsPath ∧ q.IsPath ∧ p.support.dropLast.Disjoint q.support := by
  have h : (p.append q).support = p.support.dropLast ++ q.support := by
    induction p with
    | nil => simp
    | cons hadj p ih =>
      rw [cons_append, support_cons, support_cons, ih,
        List.dropLast_cons_of_ne_nil (support_ne_nil _)]
      rfl
  have hd : p.dropLast.support.Nodup ↔ p.support.dropLast.Nodup := by
    cases p with
    | nil => simp [dropLast]
    | cons hadj p' =>
      simp only [dropLast]
      rw [take_support_eq_support_take_succ, List.dropLast_eq_take]
      have e : (cons hadj p').length - 1 + 1 = (cons hadj p').support.length - 1 := by
        first
          | simp [length_support]
          | (simp only [length_support, length_cons]; omega)
      rw [e]
  simp only [isPath_def, h, hd, List.nodup_append']
