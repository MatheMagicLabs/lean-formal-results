/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     MeasureTheory.eLpNorm_const_smul_nnreal
Source:      Mathlib @ a02a63c2, Mathlib/MeasureTheory/Function/LpSeminorm/SMul.lean, line 200
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  O2-repair-vs-resample, arm B, verified in round 0 (round 0 = first attempt)
Prover:      claude-opus-5-5
Setup:       Opus 5.5: arm B = one attempt plus up to 3 repair rounds with Lean error messages; arm A = 4 independent attempts (attempt k)
Check:       the proof replaced the human proof in the Mathlib file above; Lean reported
             0 errors and no `sorry`; sorry/admit/native_decide/search tactics were rejected.
-/

-- (context: the Mathlib file above this declaration)
lemma eLpNorm_const_smul_nnreal {f : α → ε} {c : ℝ≥0} :
    eLpNorm (c • f) p μ = ‖c‖ₑ * eLpNorm f p μ := by
  have h : ∀ (d : ℝ≥0) (g : α → ε), eLpNorm (d • g) p μ ≤ ‖d‖ₑ * eLpNorm g p μ := by
    intro d g
    by_cases hg : AEStronglyMeasurable g μ
    · exact eLpNorm_le_nnreal_smul_eLpNorm_of_ae_le_mul' (hg.const_smul d)
        (Eventually.of_forall fun _ => le_of_eq (enorm_smul ..)) _
    rw [eLpNorm_of_not_aestronglyMeasurable hg]
    rcases eq_or_ne d 0 with rfl | hd
    · simp
    · rw [ENNReal.mul_top (by simpa)]
      exact le_top
  rcases eq_or_ne c 0 with rfl | hc
  · simp
  refine le_antisymm (h c f) <| ENNReal.mul_le_of_le_div' ?_
  have h2 := h c⁻¹ (c • f)
  rw [smul_smul, inv_mul_cancel₀ hc, one_smul] at h2
  have h3 : ‖c⁻¹‖ₑ = ‖c‖ₑ⁻¹ := by
    simp [enorm_eq_nnnorm, ENNReal.coe_inv hc]
  rw [h3] at h2
  rw [ENNReal.div_eq_inv_mul]
  exact h2
