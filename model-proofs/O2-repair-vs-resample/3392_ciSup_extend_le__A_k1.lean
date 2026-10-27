/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     ciSup_extend_le
Source:      Mathlib @ a02a63c2, Mathlib/Order/ConditionallyCompleteLattice/Indexed.lean, line 127
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  O2-repair-vs-resample, arm A, attempt 1, verified in round 0 (round 0 = first attempt)
Prover:      claude-opus-5-5
Setup:       Opus 5.5: arm B = one attempt plus up to 3 repair rounds with Lean error messages; arm A = 4 independent attempts (attempt k)
Check:       the proof replaced the human proof in the Mathlib file above; Lean reported
             0 errors and no `sorry`; sorry/admit/native_decide/search tactics were rejected.
-/

-- (context: the Mathlib file above this declaration)
@[to_dual]
theorem ciSup_extend_le [Nonempty β] {f : ι → β} {g : ι → α} (hg : BddAbove (range g)) {j : β → α}
    (hj : BddAbove (range j)) :
    iSup (extend f g j) ≤ iSup g ⊔ iSup j := by
  classical
  apply ciSup_le
  intro b
  by_cases h : ∃ i, f i = b
  · rw [Function.extend_def, dif_pos h]
    exact le_sup_of_le_left (le_ciSup hg _)
  · rw [Function.extend_def, dif_neg h]
    exact le_sup_of_le_right (le_ciSup hj _)
