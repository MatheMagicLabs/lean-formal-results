/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     Finset.powerset_inter_eq_inter
Source:      Mathlib @ a02a63c2, Mathlib/Data/Finset/Sups.lean, line 389
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  O5-repair-sonnet, arm A, attempt 1, verified in round 0 (round 0 = first attempt)
Prover:      claude-sonnet-5-5
Setup:       Sonnet 5.5: arm B = repair loop; arm A = independent attempts
Check:       the proof replaced the human proof in the Mathlib file above; Lean reported
             0 errors and no `sorry`; sorry/admit/native_decide/search tactics were rejected.
-/

-- (context: the Mathlib file above this declaration)
@[simp] lemma powerset_inter_eq_inter (s t : Finset α) :
    (s ∩ t).powerset = s.powerset ∩ t.powerset := by
  ext u
  simp [subset_inter_iff]
