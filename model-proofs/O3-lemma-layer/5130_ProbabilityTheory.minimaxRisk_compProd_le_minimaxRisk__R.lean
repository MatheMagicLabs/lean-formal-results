/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     ProbabilityTheory.minimaxRisk_compProd_le_minimaxRisk
Source:      Mathlib @ a02a63c2, Mathlib/Probability/Decision/Risk/Basic.lean, line 283
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  O3-lemma-layer, arm R, verified in round 1 (round 0 = first attempt)
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
  unfold minimaxRisk
  refine le_iInf fun κ => le_iInf fun hκ => ?_
  have hfst : (P ⊗ₖ η).map Prod.fst = P := by
    first
      | (rw [← Kernel.fst_eq, Kernel.fst_compProd])
      | exact Kernel.fst_compProd P η
      | (ext θ s hs
         rw [Kernel.map_apply' _ measurable_fst _ hs,
           Kernel.compProd_apply (measurable_fst hs)]
         simp [Set.preimage, lintegral_indicator_const hs, Set.indicator])
  have h : κ.comap Prod.fst measurable_fst ∘ₖ (P ⊗ₖ η) = κ ∘ₖ P := by
    rw [← Kernel.comp_deterministic_eq_comap, Kernel.comp_assoc,
      Kernel.deterministic_comp_eq_map, hfst]
  refine (iInf_le _ (κ.comap Prod.fst measurable_fst)).trans ?_
  refine (iInf_le _ (by haveI := hκ; infer_instance)).trans ?_
  first
    | (simp only [h]; done)
    | (simp [h])
    | (rw [h])
