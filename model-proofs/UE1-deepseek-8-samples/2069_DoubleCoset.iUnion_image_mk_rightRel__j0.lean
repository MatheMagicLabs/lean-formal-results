/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     DoubleCoset.iUnion_image_mk_rightRel
Source:      Mathlib @ d0a050ad6, Mathlib/GroupTheory/DoubleCoset.lean, line 242 (group DRIFT)
Experiment:  UE1-deepseek-8-samples, arm sample 0, single attempt
Prover:      DeepSeek-Prover-V2-7B (4-bit)
Setup:       DeepSeek-Prover-V2-7B (4-bit, local), 8 independent samples per theorem, no Lean feedback;
             160 theorems: 80 DRIFT (human proof cites a lemma added after the 2025-05 snapshot) and 80 STABLE
Check:       the proof replaced the human proof in the Mathlib file above; Lean reported
             0 errors and no `sorry`.
-/

-- (context: the Mathlib file above this declaration)
lemma iUnion_image_mk_rightRel {H K : Subgroup G} :
    ⋃ q : Quotient H K, Quot.mk (rightRel H) '' doubleCoset (out q : G) H K = Set.univ := by
  have cover := iUnion_quotToDoubleCoset H K
  rw [Set.iUnion_eq_univ_iff]
  intro x
  obtain ⟨y, hy⟩ := exists_rep x
  have ⟨i, hi⟩ : ∃ i : Quotient H K, y ∈ doubleCoset (out i) H K := by
    contrapose cover
    exact (Set.ne_univ_iff_exists_notMem _).mpr ⟨y, by simpa using! cover⟩
  exact ⟨i, y, hi, hy⟩
