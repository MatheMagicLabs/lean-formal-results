/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     isDiscrete_iff_forall_mem_exists_isClosed
Source:      Mathlib @ d0a050ad6, Mathlib/Topology/DiscreteSubset.lean, line 87 (group STABLE)
Experiment:  UE1-deepseek-8-samples, arm sample 1, single attempt
Prover:      DeepSeek-Prover-V2-7B (4-bit)
Setup:       DeepSeek-Prover-V2-7B (4-bit, local), 8 independent samples per theorem, no Lean feedback;
             160 theorems: 80 DRIFT (human proof cites a lemma added after the 2025-05 snapshot) and 80 STABLE
Check:       the proof replaced the human proof in the Mathlib file above; Lean reported
             0 errors and no `sorry`.
-/

-- (context: the Mathlib file above this declaration)
theorem isDiscrete_iff_forall_mem_exists_isClosed {S : Set X} :
    IsDiscrete S ↔ ∀ s ⊆ S, ∃ U, IsClosed U ∧ U ∩ S = s := by
  simp_rw [isDiscrete_iff_discreteTopology, discreteTopology_iff_forall_isClosed,
    isClosed_induced_iff, ← image_eq_image (Subtype.val_injective), Subtype.image_preimage_coe,
    Subtype.forall_set_subtype (p := fun t ↦ ∃ U, IsClosed U ∧ S ∩ U = t), inter_comm]
