/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     IsCyclic.subgroup_eq_iff_index_eq
Source:      Mathlib @ a02a63c2, Mathlib/GroupTheory/SpecificGroups/Cyclic.lean, line 985
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  O5-repair-sonnet, arm A, attempt 3, verified in round 0 (round 0 = first attempt)
Prover:      claude-sonnet-5-5
Setup:       Sonnet 5.5: arm B = repair loop; arm A = independent attempts
Check:       the proof replaced the human proof in the Mathlib file above; Lean reported
             0 errors and no `sorry`; sorry/admit/native_decide/search tactics were rejected.
-/

-- (context: the Mathlib file above this declaration)
@[to_additive /-- In an additive cyclic group, `H = K` iff `H.index = K.index`. -/]
theorem IsCyclic.subgroup_eq_iff_index_eq :
    H = K ↔ H.index = K.index := by
  refine ⟨fun h => by rw [h], fun h => le_antisymm ?_ ?_⟩
  · exact IsCyclic.subgroup_le_iff_index_dvd.mpr h.symm.dvd
  · exact IsCyclic.subgroup_le_iff_index_dvd.mpr h.dvd
