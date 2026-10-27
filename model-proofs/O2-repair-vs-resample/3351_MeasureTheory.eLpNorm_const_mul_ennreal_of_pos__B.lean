/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     MeasureTheory.eLpNorm_const_mul_ennreal_of_pos
Source:      Mathlib @ a02a63c2, Mathlib/MeasureTheory/Function/LpSeminorm/SMul.lean, line 167
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  O2-repair-vs-resample, arm B, verified in round 1 (round 0 = first attempt)
Prover:      claude-opus-5-5
Setup:       Opus 5.5: arm B = one attempt plus up to 3 repair rounds with Lean error messages; arm A = 4 independent attempts (attempt k)
Check:       the proof replaced the human proof in the Mathlib file above; Lean reported
             0 errors and no `sorry`; sorry/admit/native_decide/search tactics were rejected.
-/

-- (context: the Mathlib file above this declaration)
theorem eLpNorm_const_mul_ennreal_of_pos {f : α → ℝ≥0∞} {c : ℝ≥0∞} (hp : 0 < p) :
    eLpNorm (fun x ↦ c * f x) p μ = c * eLpNorm f p μ := by
  by_cases hf : AEStronglyMeasurable f μ
  · exact eLpNorm_const_mul_ennreal hf
  rw [eLpNorm_of_not_aestronglyMeasurable hf]
  rcases eq_or_ne c 0 with rfl | hc
  · simp
  rw [ENNReal.mul_top hc]
  by_cases hcf : AEStronglyMeasurable (fun x => c * f x) μ
  swap
  · exact eLpNorm_of_not_aestronglyMeasurable hcf
  rcases eq_or_ne c ∞ with rfl | hc'
  · have key : eLpNorm (fun x => ∞ * f x) p μ
        = ∞ * eLpNorm (fun x => ∞ * f x) p μ := by
      rw [← eLpNorm_const_mul_ennreal hcf]
      congr 1
      funext x
      rw [← mul_assoc, ENNReal.top_mul_top]
    rcases eq_or_ne (eLpNorm (fun x => ∞ * f x) p μ) 0 with h0 | h0
    · exfalso
      first
        | rw [eLpNorm_eq_zero_iff hp.ne' hcf] at h0
        | rw [eLpNorm_eq_zero_iff hcf hp.ne'] at h0
        | rw [eLpNorm_eq_zero_iff hp.ne'] at h0
      apply hf
      refine (show AEStronglyMeasurable (fun _ => (0:ℝ≥0∞)) μ from
        aestronglyMeasurable_const).congr ?_
      filter_upwards [h0] with x hx
      simp at hx
      exact hx.symm
    · rw [key, ENNReal.top_mul h0]
  · exfalso
    apply hf
    refine ((hcf.aemeasurable.const_mul c⁻¹).aestronglyMeasurable).congr
      (Eventually.of_forall fun x => ?_)
    show c⁻¹ * (c * f x) = f x
    rw [← mul_assoc, ENNReal.inv_mul_cancel hc hc', one_mul]
