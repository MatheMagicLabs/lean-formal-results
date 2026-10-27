/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     MeasureTheory.eLpNorm_le_eLpNorm_mul_eLpNorm_ennreal_of_pos
Source:      Mathlib @ a02a63c2, Mathlib/MeasureTheory/Function/LpSeminorm/CompareExp.lean, line 601
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  O3-lemma-layer, arm RS, verified in round 1 (round 0 = first attempt)
Prover:      claude-opus-5-5
Setup:       Opus 5.5 with repair loop: arm R = repair only; arm RS = repair plus the Lean-checked lemma layer
Check:       the proof replaced the human proof in the Mathlib file above; Lean reported
             0 errors and no `sorry`; sorry/admit/native_decide/search tactics were rejected.
-/

open Filter ENNReal
open scoped Topology
namespace MeasureTheory
section SameSpace
variable {α ε ε' : Type*} {m : MeasurableSpace α} {μ : Measure α} {f : α → ε}
end SameSpace
section Bilinear
variable {α E F G ε ε' ε'' : Type*} {m : MeasurableSpace α}
open NNReal
open NNReal in
end Bilinear
section IsBoundedSMul
variable {𝕜 α E : Type*} {m : MeasurableSpace α} {μ : Measure α} [NormedRing 𝕜]
end IsBoundedSMul
section Mul
variable {α : Type*} {_ : MeasurableSpace α} {𝕜 : Type*} [NormedRing 𝕜] {μ : Measure α}

theorem eLpNorm_le_eLpNorm_mul_eLpNorm_ennreal_of_pos {f g : α → ℝ≥0∞} (hr : 0 < r)
    [hpqr : HolderTriple p q r] :
    eLpNorm (f * g) r μ ≤ eLpNorm f p μ * eLpNorm g q μ := by
  have := eLpNorm_le_eLpNorm_mul_eLpNorm_of_enorm_of_pos (μ := μ) (p := p) (q := q)
    (fun a b : ℝ≥0∞ => a * b) 1 (f := f) (g := g)
    (fun hf hg => (hf.aemeasurable.mul hg.aemeasurable).aestronglyMeasurable)
    (Filter.Eventually.of_forall fun x => by simp) hr
  rw [one_mul] at this
  exact this
