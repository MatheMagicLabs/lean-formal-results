/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     ContinuousMap.isOpen_setOfPred_range_subset
Source:      Mathlib @ d0a050ad6, Mathlib/Topology/CompactOpen.lean, line 69 (group DRIFT)
Experiment:  D1-deepseek-16-samples, arm sample 6, single attempt
Prover:      DeepSeek-Prover-V2-7B (4-bit)
Setup:       DeepSeek-Prover-V2-7B (4-bit, local), 16 independent samples per theorem, no Lean feedback;
             160 theorems: 80 DRIFT (human proof cites a lemma added after the 2025-05 snapshot) and 80 STABLE
Check:       the proof replaced the human proof in the Mathlib file above; Lean reported
             0 errors and no `sorry`.
-/

-- (context: the Mathlib file above this declaration)
lemma isOpen_setOfPred_range_subset [CompactSpace X] (hU : IsOpen U) :
    IsOpen {f : C(X, Y) | range f ⊆ U} := by
  rw [show {f : C(X, Y) | range f ⊆ U} = {f : C(X, Y) | ∀ x, f x ∈ U} by
    ext f; simp [Set.subset_def]]
  exact isOpen_generateFrom_of_mem <| by
    refine ⟨univ, isCompact_univ, ?_⟩
    simp [Set.subset_def]
    <;> aesop
