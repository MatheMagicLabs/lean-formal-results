/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     ENNReal.rpow_inv_le_iff_of_neg
Source:      Mathlib @ a02a63c2, Mathlib/Analysis/SpecialFunctions/Pow/NNReal.lean, line 826
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  O2-repair-vs-resample, arm A, attempt 1, verified in round 0 (round 0 = first attempt)
Prover:      claude-opus-5-5
Setup:       Opus 5.5: arm B = one attempt plus up to 3 repair rounds with Lean error messages; arm A = 4 independent attempts (attempt k)
Check:       the proof replaced the human proof in the Mathlib file above; Lean reported
             0 errors and no `sorry`; sorry/admit/native_decide/search tactics were rejected.
-/

-- (context: the Mathlib file above this declaration)
theorem rpow_inv_le_iff_of_neg {x y : ℝ≥0∞} {z : ℝ} (hz : z < 0) : x ^ z⁻¹ ≤ y ↔ y ^ z ≤ x := by
  nth_rw 1 [← neg_neg z, inv_neg, rpow_neg, inv_le_iff_inv_le, le_rpow_inv_iff (neg_pos.2 hz),
    inv_rpow, ← rpow_neg, neg_neg]
