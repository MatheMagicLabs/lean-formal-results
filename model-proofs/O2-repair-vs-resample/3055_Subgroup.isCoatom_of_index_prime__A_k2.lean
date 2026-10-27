/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     Subgroup.isCoatom_of_index_prime
Source:      Mathlib @ a02a63c2, Mathlib/GroupTheory/IndexNormal.lean, line 37
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  O2-repair-vs-resample, arm A, attempt 2, verified in round 0 (round 0 = first attempt)
Prover:      claude-opus-5-5
Setup:       Opus 5.5: arm B = one attempt plus up to 3 repair rounds with Lean error messages; arm A = 4 independent attempts (attempt k)
Check:       the proof replaced the human proof in the Mathlib file above; Lean reported
             0 errors and no `sorry`; sorry/admit/native_decide/search tactics were rejected.
-/

-- (context: the Mathlib file above this declaration)
@[to_additive]
theorem isCoatom_of_index_prime (hH : H.index.Prime) : IsCoatom H := by
  refine ⟨fun h => ?_, fun K hK => ?_⟩
  · rw [h, index_top] at hH
    exact Nat.not_prime_one hH
  · rw [← relIndex_mul_index hK.le, Nat.prime_mul_iff] at hH
    rcases hH with ⟨_, h⟩ | ⟨_, h⟩
    · exact index_eq_one.mp h
    · exact absurd (relIndex_eq_one.mp h) (not_le_of_gt hK)
