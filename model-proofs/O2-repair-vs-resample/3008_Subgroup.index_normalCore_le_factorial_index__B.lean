/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     Subgroup.index_normalCore_le_factorial_index
Source:      Mathlib @ a02a63c2, Mathlib/GroupTheory/IndexNormal.lean, line 100
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  O2-repair-vs-resample, arm B, verified in round 0 (round 0 = first attempt)
Prover:      claude-opus-5-5
Setup:       Opus 5.5: arm B = one attempt plus up to 3 repair rounds with Lean error messages; arm A = 4 independent attempts (attempt k)
Check:       the proof replaced the human proof in the Mathlib file above; Lean reported
             0 errors and no `sorry`; sorry/admit/native_decide/search tactics were rejected.
-/

-- (context: the Mathlib file above this declaration)
@[to_additive]
theorem index_normalCore_le_factorial_index : H.normalCore.index ≤ H.index ! := by
  by_cases h : H.FiniteIndex
  · haveI := h
    exact Nat.le_of_dvd (factorial_pos _) (index_normalCore_dvd_factorial_index H)
  · have h0 : H.index = 0 := by
      by_contra hne
      exact h ⟨hne⟩
    have h1 : H.normalCore.index = 0 := by
      have := index_dvd_of_le H.normalCore_le
      rw [h0] at this
      exact Nat.eq_zero_of_zero_dvd this
    rw [h1]
    exact Nat.zero_le _
