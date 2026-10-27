/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     MeasureTheory.eLpNormEssSup_add_measure
Source:      Mathlib @ a02a63c2, Mathlib/MeasureTheory/Function/LpSeminorm/Basic.lean, line 972
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  O3-lemma-layer, arm RS, verified in round 3 (round 0 = first attempt)
Prover:      claude-opus-5-5
Setup:       Opus 5.5 with repair loop: arm R = repair only; arm RS = repair plus the Lean-checked lemma layer
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

lemma eLpNormEssSup_add_measure {ε : Type*} [TopologicalSpace ε] [ContinuousENorm ε] {f : α → ε} :
    eLpNormEssSup f (μ + ν) = max (eLpNormEssSup f μ) (eLpNormEssSup f ν) := by
  simp only [eLpNormEssSup]
  have h1 : μ ≪ μ + ν := fun s hs => by
    rw [Measure.add_apply] at hs
    exact (add_eq_zero.mp hs).1
  have h2 : ν ≪ μ + ν := fun s hs => by
    rw [Measure.add_apply] at hs
    exact (add_eq_zero.mp hs).2
  apply le_antisymm
  · have h : (fun x => ‖f x‖ₑ) ≤ᵐ[μ + ν]
        fun _ => max (essSup (fun x => ‖f x‖ₑ) μ) (essSup (fun x => ‖f x‖ₑ) ν) := by
      refine ae_add_measure_iff.mpr ⟨?_, ?_⟩
      · exact (ae_le_essSup (f := fun x => ‖f x‖ₑ) (μ := μ)).mono
          fun x hx => hx.trans (le_max_left _ _)
      · exact (ae_le_essSup (f := fun x => ‖f x‖ₑ) (μ := ν)).mono
          fun x hx => hx.trans (le_max_right _ _)
    first
      | exact essSup_le_of_ae_le _ h
      | exact essSup_le_of_ae_le h
  · apply max_le
    · exact essSup_mono_measure h1
    · exact essSup_mono_measure h2
