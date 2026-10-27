/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     Seminorm.bound_sum_of_continuous
Source:      Mathlib @ a02a63c2, Mathlib/Analysis/LocallyConvex/WithSeminorms.lean, line 1026
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  O5-repair-sonnet, arm A, attempt 2, verified in round 0 (round 0 = first attempt)
Prover:      claude-sonnet-5-5
Setup:       Sonnet 5.5: arm B = repair loop; arm A = independent attempts
Check:       the proof replaced the human proof in the Mathlib file above; Lean reported
             0 errors and no `sorry`; sorry/admit/native_decide/search tactics were rejected.
-/

-- (context: the Mathlib file above this declaration)
lemma bound_sum_of_continuous [t : TopologicalSpace E] (hp : WithSeminorms p)
    (q : Seminorm 𝕜 E) (hq : Continuous q) :
    ∃ s : Finset ι, ∃ C : ℝ≥0, C ≠ 0 ∧ q ≤ C • ∑ i ∈ s, p i := by
  obtain ⟨s, C, hC, h⟩ := bound_of_continuous hp q hq
  exact ⟨s, C, hC, h.trans (IsOrderedSMul.smul_le_smul_left _ _ (finset_sup_le_sum p s) C)⟩
