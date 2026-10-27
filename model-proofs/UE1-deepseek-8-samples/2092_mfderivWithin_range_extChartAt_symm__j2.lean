/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     mfderivWithin_range_extChartAt_symm
Source:      Mathlib @ d0a050ad6, Mathlib/Geometry/Manifold/MFDeriv/Atlas.lean, line 459 (group STABLE)
Experiment:  UE1-deepseek-8-samples, arm sample 2, single attempt
Prover:      DeepSeek-Prover-V2-7B (4-bit)
Setup:       DeepSeek-Prover-V2-7B (4-bit, local), 8 independent samples per theorem, no Lean feedback;
             160 theorems: 80 DRIFT (human proof cites a lemma added after the 2025-05 snapshot) and 80 STABLE
Check:       the proof replaced the human proof in the Mathlib file above; Lean reported
             0 errors and no `sorry`.
-/

-- (context: the Mathlib file above this declaration)
lemma mfderivWithin_range_extChartAt_symm :
    mfderiv[range I] (extChartAt I x).symm (extChartAt I x x) = ContinuousLinearMap.id 𝕜 _ := by
  rw [← TangentBundle.symmL_trivializationAt (by simp),
    TangentBundle.symmL_trivializationAt_eq_core (by simp)]
  ext v
  simpa using! (tangentBundleCore I M).coordChange_self (achart H x) x (mem_chart_source H x) v
