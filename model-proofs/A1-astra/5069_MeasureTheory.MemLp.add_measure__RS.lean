/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     MeasureTheory.MemLp.add_measure
Source:      Mathlib @ a02a63c2, Mathlib/MeasureTheory/Function/LpSeminorm/Basic.lean, line 984
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  A1-astra, arm RS, verified in round 2 (round 0 = first attempt)
Prover:      gpt-6-astra
Setup:       GPT-6 Astra (Codex, effort medium): R = proof plus up to 3 repair rounds with Lean errors; RS = R plus lemma layer; RT = R with read-only Mathlib sources to search; N0-N3 = independent attempts
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
  have hμm := h1.aestronglyMeasurable
  have hνm := h2.aestronglyMeasurable
  have hsum := hμm.add_measure hνm
  change eLpNorm f p (μ + ν) < ∞
  have hμ : eLpNorm f p μ < ∞ := h1
  have hν : eLpNorm f p ν < ∞ := h2
  by_cases hp0 : p = 0
  · simp [hp0, eLpNorm_exponent_zero, hsum]
  by_cases hp_top : p = ∞
  · simp only [hp_top, eLpNorm_exponent_top, hμm, hνm, hsum] at hμ hν ⊢
    rw [eLpNormEssSup_add_measure]
    exact max_lt hμ hν
  · rw [eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top hp0 hp_top] at hμ hν ⊢ <;>
      try assumption
    rw [lintegral_add_measure]
    exact ENNReal.add_lt_top.2 ⟨hμ, hν⟩
