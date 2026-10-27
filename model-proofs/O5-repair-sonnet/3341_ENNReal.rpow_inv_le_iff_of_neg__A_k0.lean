/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     ENNReal.rpow_inv_le_iff_of_neg
Source:      Mathlib @ a02a63c2, Mathlib/Analysis/SpecialFunctions/Pow/NNReal.lean, line 826
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  O5-repair-sonnet, arm A, attempt 0, verified in round 0 (round 0 = first attempt)
Prover:      claude-sonnet-5-5
Setup:       Sonnet 5.5: arm B = repair loop; arm A = independent attempts
Check:       the proof replaced the human proof in the Mathlib file above; Lean reported
             0 errors and no `sorry`; sorry/admit/native_decide/search tactics were rejected.
-/

-- (context: the Mathlib file above this declaration)
theorem rpow_inv_le_iff_of_neg {x y : ℝ≥0∞} {z : ℝ} (hz : z < 0) : x ^ z⁻¹ ≤ y ↔ y ^ z ≤ x := by
  have h : x ^ z⁻¹ = (x ^ (-z)⁻¹)⁻¹ := by
    rw [← rpow_neg, ← inv_neg, neg_neg]
  rw [h, ENNReal.inv_le_iff_inv_le, le_rpow_inv_iff (neg_pos.2 hz), inv_rpow, ← rpow_neg, neg_neg]
