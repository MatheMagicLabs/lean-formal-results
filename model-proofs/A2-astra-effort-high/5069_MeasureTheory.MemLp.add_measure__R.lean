/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     MeasureTheory.MemLp.add_measure
Source:      Mathlib @ a02a63c2, Mathlib/MeasureTheory/Function/LpSeminorm/Basic.lean, line 984
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  A2-astra-effort-high, arm R, verified in round 3 (round 0 = first attempt)
Prover:      gpt-6-astra
Setup:       GPT-6 Astra, reasoning effort high (arms R, N0)
Check:       the proof replaced the human proof in the Mathlib file above; Lean reported
             0 errors and no `sorry`; sorry/admit/native_decide/search tactics were rejected.
-/

open TopologicalSpace MeasureTheory Filter
open scoped NNReal ENNReal Topology ComplexConjugate
variable {α ε ε' ε'' E F G : Type*} {m m0 : MeasurableSpace α} {p : ℝ≥0∞} {q : ℝ} {μ ν : Measure α}
namespace MeasureTheory
section Lp
section Top
end Top
section Zero
section ESeminormedAddMonoid
variable {ε : Type*} [TopologicalSpace ε] [ESeminormedAddMonoid ε]
variable [MeasurableSpace α]
end ESeminormedAddMonoid
end Zero
section Neg
end Neg
section Const
end Const
variable {f : α → F}
open scoped symmDiff in
section ENormedAddMonoid
variable {ε : Type*} [TopologicalSpace ε] [ENormedAddMonoid ε]
end ENormedAddMonoid
section SMul
variable {R : Type*} [Semiring R] [IsDomain R] [Module R ℝ≥0∞] [IsScalarTower R ℝ≥0∞ ℝ≥0∞]
end SMul
variable {ε : Type*} [TopologicalSpace ε] [ENorm ε] [PseudoMetrizableSpace ε] in
variable {ε : Type*} [ENorm ε] in
variable {ε : Type*} [ENorm ε] in
section ESeminormedAddMonoid
variable {ε : Type*} [TopologicalSpace ε] [ESeminormedAddMonoid ε]
variable {ε : Type*} [ENorm ε] in
variable {ε : Type*} [ENorm ε] in
end ESeminormedAddMonoid
section ENormedAddMonoid
variable {ε : Type*} [TopologicalSpace ε] [ENormedAddMonoid ε]
variable {ε : Type*} [ENorm ε] in

lemma MemLp.add_measure (h1 : MemLp f p μ) (h2 : MemLp f p ν) : MemLp f p (μ + ν) := by
  have hμ := h1.aestronglyMeasurable
  have hν := h2.aestronglyMeasurable
  have hf := hμ.add_measure hν
  change eLpNorm f p (μ + ν) < ∞
  change eLpNorm f p μ < ∞ at h1
  change eLpNorm f p ν < ∞ at h2
  rcases eq_or_ne p 0 with rfl | hp0
  · simp [eLpNorm, hf]
  rcases eq_or_ne p ∞ with rfl | hp_top
  · simp_all only [eLpNorm_exponent_top,
      eLpNormEssSup_add_measure, max_lt_iff]
    exact ⟨True.intro, True.intro⟩
  · rw [eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top hp0 hp_top hf,
      lintegral_add_measure]
    exact ENNReal.add_lt_top.mpr
      ⟨(eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top hp0 hp_top hμ).mp h1,
       (eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top hp0 hp_top hν).mp h2⟩
