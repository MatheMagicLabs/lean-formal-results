/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     ModelWithCorners.extendCoordChange_target
Source:      Mathlib @ d0a050ad6, Mathlib/Geometry/Manifold/IsManifold/ExtChartAt.lean, line 341 (group DRIFT)
Experiment:  UE1-deepseek-8-samples, arm sample 0, single attempt
Prover:      DeepSeek-Prover-V2-7B (4-bit)
Setup:       DeepSeek-Prover-V2-7B (4-bit, local), 8 independent samples per theorem, no Lean feedback;
             160 theorems: 80 DRIFT (human proof cites a lemma added after the 2025-05 snapshot) and 80 STABLE
Check:       the proof replaced the human proof in the Mathlib file above; Lean reported
             0 errors and no `sorry`.
-/

-- (context: the Mathlib file above this declaration)
lemma extendCoordChange_target :
    (I.extendCoordChange e e').target = I '' (e.symm ≫ₕ e').target := by
  simp_rw [extendCoordChange, PartialEquiv.trans_target, I.image_eq, e'.extend_target,
    PartialEquiv.symm_target, e.extend_source, inter_right_comm _ (range I)]
  simp [Set.preimage_comp]
