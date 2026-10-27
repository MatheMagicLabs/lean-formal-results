/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     ENNReal.le_rpow_inv_iff_of_neg
Source:      Mathlib @ a02a63c2, Mathlib/Analysis/SpecialFunctions/Pow/NNReal.lean, line 822
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  O2-repair-vs-resample, arm A, attempt 3, verified in round 0 (round 0 = first attempt)
Prover:      claude-opus-5-5
Setup:       Opus 5.5: arm B = one attempt plus up to 3 repair rounds with Lean error messages; arm A = 4 independent attempts (attempt k)
Check:       the proof replaced the human proof in the Mathlib file above; Lean reported
             0 errors and no `sorry`; sorry/admit/native_decide/search tactics were rejected.
-/

-- (context: the Mathlib file above this declaration)
theorem le_rpow_inv_iff_of_neg {x y : ℝ≥0∞} {z : ℝ} (hz : z < 0) : x ≤ y ^ z⁻¹ ↔ y ≤ x ^ z := by
  have hz' : 0 < -z := neg_pos.mpr hz
  have h1 : y ^ z⁻¹ = y⁻¹ ^ (-z)⁻¹ := by
    rw [inv_rpow, ← rpow_neg, inv_neg, neg_neg]
  rw [h1, le_rpow_inv_iff hz', ENNReal.le_inv_iff_le_inv, ← rpow_neg, neg_neg]
