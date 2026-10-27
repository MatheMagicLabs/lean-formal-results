/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     Subgroup.index_normalCore_le_factorial_index
Source:      Mathlib @ a02a63c2, Mathlib/GroupTheory/IndexNormal.lean, line 100
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  O2-repair-vs-resample, arm A, attempt 0, verified in round 0 (round 0 = first attempt)
Prover:      claude-opus-5-5
Setup:       Opus 5.5: arm B = one attempt plus up to 3 repair rounds with Lean error messages; arm A = 4 independent attempts (attempt k)
Check:       the proof replaced the human proof in the Mathlib file above; Lean reported
             0 errors and no `sorry`; sorry/admit/native_decide/search tactics were rejected.
-/

-- (context: the Mathlib file above this declaration)
@[to_additive]
theorem index_normalCore_le_factorial_index : H.normalCore.index ≤ H.index ! := by
  by_cases h : H.index = 0
  · have h2 := index_dvd_of_le H.normalCore_le
    rw [h, zero_dvd_iff] at h2
    rw [h2]
    exact Nat.zero_le _
  · have : H.FiniteIndex := ⟨h⟩
    exact Nat.le_of_dvd (Nat.factorial_pos _) (index_normalCore_dvd_factorial_index H)
