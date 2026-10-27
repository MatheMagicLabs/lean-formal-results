/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     MeasureTheory.eLpNorm'_le_eLpNorm'_mul_eLpNorm'_of_enorm
Source:      Mathlib @ a02a63c2, Mathlib/MeasureTheory/Function/LpSeminorm/CompareExp.lean, line 392
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

theorem eLpNorm'_le_eLpNorm'_mul_eLpNorm'_of_enorm {p q r : ℝ}
    (b : ε → ε' → ε'') (c : ℝ≥0∞) {f : α → ε} {g : α → ε'}
    (hf : AEStronglyMeasurable f μ) (hg : AEStronglyMeasurable g μ)
    (h : ∀ᵐ x ∂μ, ‖b (f x) (g x)‖ₑ ≤ c * ‖f x‖ₑ * ‖g x‖ₑ)
    (hpqr : Real.HolderTriple p q r) :
    eLpNorm' (fun x => b (f x) (g x)) r μ ≤ c * eLpNorm' f p μ * eLpNorm' g q μ := by
  have hp : 0 < p := hpqr.left_pos
  have hq : 0 < q := hpqr.right_pos
  have hr : 0 < r := by
    rw [← hpqr.inv_inv_add_inv]
    exact inv_pos.2 (add_pos (inv_pos.2 hp) (inv_pos.2 hq))
  have key : eLpNorm' (fun x => ‖f x‖ₑ * ‖g x‖ₑ) r μ ≤ eLpNorm' f p μ * eLpNorm' g q μ := by
    unfold eLpNorm'
    simp only [enorm_eq_self]
    exact ENNReal.lintegral_Lp_mul_le_Lq_mul_Lr hpqr μ hf.enorm hg.enorm
  calc
    eLpNorm' (fun x => b (f x) (g x)) r μ
        ≤ c * eLpNorm' (fun x => ‖f x‖ₑ * ‖g x‖ₑ) r μ := by
      apply eLpNorm'_le_mul_eLpNorm'_of_ae_le_mul
        (hf.enorm.mul hg.enorm).aestronglyMeasurable _ hr
      filter_upwards [h] with x hx
      simpa [mul_assoc] using hx
    _ ≤ c * (eLpNorm' f p μ * eLpNorm' g q μ) := by
      gcongr
    _ = c * eLpNorm' f p μ * eLpNorm' g q μ := (mul_assoc _ _ _).symm
