/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     MeasureTheory.eLpNorm_const_smul_nnreal
Source:      Mathlib @ a02a63c2, Mathlib/MeasureTheory/Function/LpSeminorm/SMul.lean, line 200
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  O3-lemma-layer, arm R, verified in round 1 (round 0 = first attempt)
Prover:      claude-opus-5-5
Setup:       Opus 5.5 with repair loop: arm R = repair only; arm RS = repair plus the Lean-checked lemma layer
Check:       the proof replaced the human proof in the Mathlib file above; Lean reported
             0 errors and no `sorry`; sorry/admit/native_decide/search tactics were rejected.
-/

open Filter
open scoped ENNReal NNReal Topology
namespace MeasureTheory
variable {α F : Type*} {m : MeasurableSpace α} {p : ℝ≥0∞} {q : ℝ} {μ : Measure α}
section Lp
section IsBoundedSMul
variable {𝕜 : Type*} [NormedRing 𝕜] [MulActionWithZero 𝕜 F] [IsBoundedSMul 𝕜 F] {c : 𝕜}
end IsBoundedSMul
section ENormSMulClass
variable {𝕜 : Type*} [NormedRing 𝕜]
end ENormSMulClass
section ENormSMulClass
variable {𝕜 : Type*} [NormedRing 𝕜]
end ENormSMulClass
section NormedSpace
variable {𝕜 : Type*} [NormedDivisionRing 𝕜] [Module 𝕜 F] [NormSMulClass 𝕜 F]
end NormedSpace
section ENNReal
end ENNReal
section NNReal
variable {ε : Type*} [TopologicalSpace ε] [ENormedAddMonoid ε] [MulActionWithZero ℝ≥0 ε]

lemma eLpNorm_const_smul_nnreal {f : α → ε} {c : ℝ≥0} :
    eLpNorm (c • f) p μ = ‖c‖ₑ * eLpNorm f p μ := by
  by_cases hc : c = 0
  · subst hc
    simp
  by_cases hf : AEStronglyMeasurable f μ
  · have hcf : AEStronglyMeasurable (c • f) μ := hf.const_smul c
    simp only [eLpNorm, hf, hcf, ↓reduceIte]
    simp only [eLpNorm', eLpNormEssSup, Pi.smul_apply, enorm_smul]
    split_ifs with h1 h2
    · simp
    · exact ENNReal.essSup_const_mul
    · have hp : 0 < p.toReal := ENNReal.toReal_pos h1 h2
      simp_rw [ENNReal.mul_rpow_of_nonneg _ _ hp.le]
      rw [lintegral_const_mul' _ _ (ENNReal.rpow_ne_top_of_nonneg hp.le enorm_ne_top),
        ENNReal.mul_rpow_of_nonneg _ _ (by positivity),
        ← ENNReal.rpow_mul, mul_one_div_cancel hp.ne', ENNReal.rpow_one]
  · have hcf : ¬AEStronglyMeasurable (c • f) μ := by
      intro h
      apply hf
      have := h.const_smul c⁻¹
      rwa [smul_smul, inv_mul_cancel₀ hc, one_smul] at this
    simp [eLpNorm, hf, hcf, ENNReal.mul_top, hc]
