/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     Mathlib.Tactic.Echelon.pivotOfList_mono_of_sortedLT
Source:      Mathlib @ a02a63c2, Mathlib/Tactic/Echelon/Reflection.lean, line 122
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  O5-repair-sonnet, arm A, attempt 1, verified in round 0 (round 0 = first attempt)
Prover:      claude-sonnet-5-5
Setup:       Sonnet 5.5: arm B = repair loop; arm A = independent attempts
Check:       the proof replaced the human proof in the Mathlib file above; Lean reported
             0 errors and no `sorry`; sorry/admit/native_decide/search tactics were rejected.
-/

-- (context: the Mathlib file above this declaration)
theorem pivotOfList_mono_of_sortedLT {cols : List (Fin n)} (hsorted : cols.SortedLT) :
    Monotone (pivotOfList cols) := by
  intro i j hij
  rcases hij.eq_or_lt with rfl | hlt
  · exact le_rfl
  · by_cases hj : pivotOfList cols j = ⊤
    · rw [hj]; exact le_top
    · exact (pivotOfList_lt_pivotOfList hsorted hlt hj).le
