/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     MeasureTheory.ofMultiset_apply_singleton
Source:      Mathlib @ a02a63c2, Mathlib/Probability/Distributions/Uniform.lean, line 306
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  O2-repair-vs-resample, arm A, attempt 0, verified in round 0 (round 0 = first attempt)
Prover:      claude-opus-5-5
Setup:       Opus 5.5: arm B = one attempt plus up to 3 repair rounds with Lean error messages; arm A = 4 independent attempts (attempt k)
Check:       the proof replaced the human proof in the Mathlib file above; Lean reported
             0 errors and no `sorry`; sorry/admit/native_decide/search tactics were rejected.
-/

-- (context: the Mathlib file above this declaration)
@[simp]
theorem ofMultiset_apply_singleton (a : α) : ofMultiset s {a} = s.count a / (Multiset.card s) := by
  rw [ofMultiset, finsetSum_apply]
  by_cases ha : a ∈ s.toFinset
  · rw [Finset.sum_eq_single_of_mem a ha]
    · simp [dirac_apply, Set.indicator]
    · intro b hb hba
      simp [dirac_apply, Set.indicator, hba]
  · have ha' : a ∉ s := by simpa using ha
    rw [Finset.sum_eq_zero]
    · simp [Multiset.count_eq_zero.mpr ha']
    · intro b hb
      have hba : b ≠ a := by
        rintro rfl
        exact ha hb
      simp [dirac_apply, Set.indicator, hba]
