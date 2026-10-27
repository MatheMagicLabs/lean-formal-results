/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     MeasureTheory.eLpNorm_const_mul_ennreal_of_pos
Source:      Mathlib @ a02a63c2, Mathlib/MeasureTheory/Function/LpSeminorm/SMul.lean, line 167
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  A1-astra, arm RT, verified in round 0 (round 0 = first attempt)
Prover:      gpt-6-astra
Setup:       GPT-6 Astra (Codex, effort medium): R = proof plus up to 3 repair rounds with Lean errors; RS = R plus lemma layer; RT = R with read-only Mathlib sources to search; N0-N3 = independent attempts
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
  rcases eq_or_ne c 0 with rfl | hc
  · simp
  rw [eLpNorm_of_not_aestronglyMeasurable hf, ENNReal.mul_top hc]
  by_cases hcf : AEStronglyMeasurable (fun x ↦ c * f x) μ
  · rcases eq_or_ne c ∞ with rfl | hc_top
    · have hne : eLpNorm (fun x ↦ ∞ * f x) p μ ≠ 0 := by
        intro h
        have hz := (eLpNorm_eq_zero_iff hp.ne').mp h
        apply hf
        refine ⟨0, stronglyMeasurable_zero, ?_⟩
        filter_upwards [hz] with x hx
        simpa only [Pi.zero_apply, mul_eq_zero, ENNReal.top_ne_zero,
          false_or] using hx
      have h := eLpNorm_const_mul_ennreal (c := ∞) (p := p) hcf
      simpa [← mul_assoc, ENNReal.top_mul hne] using h
    · exfalso
      apply hf
      simpa only [← mul_assoc, ENNReal.inv_mul_cancel hc hc_top, one_mul] using
        (hcf.aemeasurable.const_mul c⁻¹).aestronglyMeasurable
  · exact eLpNorm_of_not_aestronglyMeasurable hcf
