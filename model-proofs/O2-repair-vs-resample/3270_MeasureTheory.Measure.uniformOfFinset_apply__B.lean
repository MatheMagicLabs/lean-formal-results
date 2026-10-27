/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     MeasureTheory.Measure.uniformOfFinset_apply
Source:      Mathlib @ a02a63c2, Mathlib/Probability/Distributions/Uniform.lean, line 250
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  O2-repair-vs-resample, arm B, verified in round 1 (round 0 = first attempt)
Prover:      claude-opus-5-5
Setup:       Opus 5.5: arm B = one attempt plus up to 3 repair rounds with Lean error messages; arm A = 4 independent attempts (attempt k)
Check:       the proof replaced the human proof in the Mathlib file above; Lean reported
             0 errors and no `sorry`; sorry/admit/native_decide/search tactics were rejected.
-/

-- (context: the Mathlib file above this declaration)
theorem uniformOfFinset_apply :
    uniformOfFinset s t = #{x ∈ s | x ∈ t} / #s :=
  calc
    uniformOfFinset s t = ∑ x ∈ s with x ∈ t, (#s : ℝ≥0∞)⁻¹ := by
      rw [uniformOfFinset, finsetSum_apply]
      have h : ∀ a ∈ s, ((#s : ℝ≥0∞)⁻¹ • dirac a) t
          = if a ∈ t then (#s : ℝ≥0∞)⁻¹ else 0 := by
        intro a _
        rw [Measure.smul_apply, dirac_apply, smul_eq_mul]
        by_cases ha : a ∈ t <;> simp [ha]
      rw [Finset.sum_congr rfl h, ← Finset.sum_filter]
        _ = #{x ∈ s | x ∈ t} / #s := by
          rw [Finset.sum_const, nsmul_eq_mul, div_eq_mul_inv]
