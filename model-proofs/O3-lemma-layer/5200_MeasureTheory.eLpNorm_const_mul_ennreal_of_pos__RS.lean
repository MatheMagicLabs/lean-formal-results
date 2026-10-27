/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     MeasureTheory.eLpNorm_const_mul_ennreal_of_pos
Source:      Mathlib @ a02a63c2, Mathlib/MeasureTheory/Function/LpSeminorm/SMul.lean, line 167
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  O3-lemma-layer, arm RS, verified in round 3 (round 0 = first attempt)
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

theorem eLpNorm_const_mul_ennreal_of_pos {f : α → ℝ≥0∞} {c : ℝ≥0∞} (hp : 0 < p) :
    eLpNorm (fun x ↦ c * f x) p μ = c * eLpNorm f p μ := by
  by_cases hf : AEStronglyMeasurable f μ
  · exact eLpNorm_const_mul_ennreal hf
  have hfinf : eLpNorm f p μ = ∞ := by
    simp [eLpNorm, eLpNorm', eLpNormEssSup, hf, hp.ne']
  rcases eq_or_ne c 0 with rfl | hc0
  · simp
  rw [hfinf, ENNReal.mul_top hc0]
  by_cases hg : AEStronglyMeasurable (fun x => c * f x) μ
  swap
  · simp [eLpNorm, eLpNorm', eLpNormEssSup, hg, hp.ne']
  rcases eq_or_ne c ∞ with rfl | hctop
  · have key : eLpNorm (fun x => ∞ * f x) p μ = ∞ * eLpNorm (fun x => ∞ * f x) p μ := by
      rw [← eLpNorm_const_mul_ennreal hg]
      congr 1
      funext x
      rw [← mul_assoc, ENNReal.top_mul_top]
    rcases eq_or_ne (eLpNorm (fun x => ∞ * f x) p μ) 0 with h0 | h0
    · exfalso
      have h0' : (fun x => ∞ * f x) =ᵐ[μ] 0 := by
        first
          | exact (eLpNorm_eq_zero_iff hp.ne').mp h0
          | exact ((eLpNorm_eq_zero_iff hp.ne').mp h0).2
          | exact (eLpNorm_eq_zero_iff hg hp.ne').mp h0
      apply hf
      refine aestronglyMeasurable_zero.congr ?_
      filter_upwards [h0'] with x hx
      simp at hx
      simp [hx]
    · rw [key]
      exact ENNReal.top_mul h0
  · exfalso
    apply hf
    have : (fun x => c⁻¹ * (c * f x)) = f := by
      funext x
      rw [← mul_assoc, ENNReal.inv_mul_cancel hc0 hctop, one_mul]
    rw [← this]
    exact (hg.aemeasurable.const_mul c⁻¹).aestronglyMeasurable
