/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     MeasureTheory.eLpNorm'_le_eLpNorm'_mul_eLpNorm'_of_enorm
Source:      Mathlib @ a02a63c2, Mathlib/MeasureTheory/Function/LpSeminorm/CompareExp.lean, line 392
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  A1-astra, arm RS, verified in round 3 (round 0 = first attempt)
Prover:      gpt-6-astra
Setup:       GPT-6 Astra (Codex, effort medium): R = proof plus up to 3 repair rounds with Lean errors; RS = R plus lemma layer; RT = R with read-only Mathlib sources to search; N0-N3 = independent attempts
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
  have hr : 0 < r := by
    rcases hpqr with ⟨he, hp, hq⟩
    have hi : 0 < r⁻¹ := by
      rw [← he]
      positivity
    exact inv_pos.mp hi
  calc
    eLpNorm' (fun x => b (f x) (g x)) r μ ≤
        c * eLpNorm' (fun x => ‖f x‖ₑ * ‖g x‖ₑ) r μ :=
      eLpNorm'_le_mul_eLpNorm'_of_ae_le_mul
        (hf.enorm.mul hg.enorm).aestronglyMeasurable
        (by simpa only [enorm_eq_self, mul_assoc] using h) hr
    _ ≤ c * (eLpNorm' f p μ * eLpNorm' g q μ) := by
      apply mul_le_mul_right
      unfold eLpNorm'
      simp only [enorm_eq_self]
      apply ENNReal.lintegral_Lp_mul_le_Lq_mul_Lr <;>
        first
        | exact hpqr
        | exact hf.enorm
        | exact hg.enorm
        | exact hr
    _ = c * eLpNorm' f p μ * eLpNorm' g q μ := (mul_assoc _ _ _).symm
