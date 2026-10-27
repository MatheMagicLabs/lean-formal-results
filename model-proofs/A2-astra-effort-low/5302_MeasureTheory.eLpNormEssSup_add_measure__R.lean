/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     MeasureTheory.eLpNormEssSup_add_measure
Source:      Mathlib @ a02a63c2, Mathlib/MeasureTheory/Function/LpSeminorm/Basic.lean, line 972
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  A2-astra-effort-low, arm R, verified in round 3 (round 0 = first attempt)
Prover:      gpt-6-astra
Setup:       GPT-6 Astra, reasoning effort low (arms R, N0)
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
  unfold eLpNormEssSup
  have h (ρ : Measure α) (c : ℝ≥0∞) :
      essSup (fun x => ‖f x‖ₑ) ρ ≤ c ↔
        ∀ᵐ x ∂ρ, ‖f x‖ₑ ≤ c := by
    constructor
    · intro hc
      have hb : ∀ᵐ x ∂ρ, ‖f x‖ₑ ≤ essSup (fun x => ‖f x‖ₑ) ρ := by
        apply ae_le_essSup
        isBoundedDefault
      exact hb.mono fun x hx => hx.trans hc
    · intro hc
      apply essSup_le_of_ae_le
      · exact hc
      · isBoundedDefault
  have H (c : ℝ≥0∞) :
      essSup (fun x => ‖f x‖ₑ) (μ + ν) ≤ c ↔
        max (essSup (fun x => ‖f x‖ₑ) μ)
          (essSup (fun x => ‖f x‖ₑ) ν) ≤ c := by
    simp only [max_le_iff, h, ae_add_measure_iff]
  exact le_antisymm ((H _).mpr le_rfl) ((H _).mp le_rfl)
