/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     ProbabilityTheory.minimaxRisk_compProd_le_minimaxRisk
Source:      Mathlib @ a02a63c2, Mathlib/Probability/Decision/Risk/Basic.lean, line 283
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  O3-lemma-layer, arm RS, verified in round 2 (round 0 = first attempt)
Prover:      claude-opus-5-5
Setup:       Opus 5.5 with repair loop: arm R = repair only; arm RS = repair plus the Lean-checked lemma layer
Check:       the proof replaced the human proof in the Mathlib file above; Lean reported
             0 errors and no `sorry`; sorry/admit/native_decide/search tactics were rejected.
-/

open MeasureTheory Function
open scoped ENNReal NNReal
namespace ProbabilityTheory
variable {Θ 𝓧 𝓧' 𝓨 : Type*} {mΘ : MeasurableSpace Θ}
section BayesRiskLeMinimaxRisk
end BayesRiskLeMinimaxRisk
section Const
end Const
section Bounds
end Bounds
section Subsingleton
variable [Subsingleton 𝓧] [Nonempty 𝓨]
end Subsingleton
section Compositions

lemma minimaxRisk_compProd_le_minimaxRisk (ℓ : Θ → 𝓨 → ℝ≥0∞) (P : Kernel Θ 𝓧)
    [IsSFiniteKernel P] (η : Kernel (Θ × 𝓧) 𝓧') [IsMarkovKernel η] :
    minimaxRisk ℓ (P ⊗ₖ η) ≤ minimaxRisk ℓ P := by
  have h : minimaxRisk ℓ (P ⊗ₖ η) ≤ minimaxRisk ℓ ((P ⊗ₖ η).map Prod.fst) :=
    minimaxRisk_le_minimaxRisk_map ℓ (P ⊗ₖ η) measurable_fst
  have h2 : (P ⊗ₖ η).map Prod.fst = P := by
    first
    | (ext x : 1
       rw [Kernel.map_apply _ measurable_fst]
       have h3 : ((P ⊗ₖ η) x).map Prod.fst = ((P ⊗ₖ η) x).fst := rfl
       rw [h3, ← Kernel.fst_apply, Kernel.fst_compProd])
    | (rw [← Kernel.fst_eq]; exact Kernel.fst_compProd P η)
    | (ext x : 1
       rw [Kernel.map_apply _ measurable_fst]
       have h3 : ((P ⊗ₖ η) x).map Prod.fst = ((P ⊗ₖ η) x).fst := rfl
       rw [h3, ← Kernel.fst_apply]
       simp)
  rwa [h2] at h
