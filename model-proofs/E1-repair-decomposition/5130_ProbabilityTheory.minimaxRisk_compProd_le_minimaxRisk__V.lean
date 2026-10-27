/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     ProbabilityTheory.minimaxRisk_compProd_le_minimaxRisk
Source:      Mathlib @ a02a63c2, Mathlib/Probability/Decision/Risk/Basic.lean, line 283
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  E1-repair-decomposition, arm V, verified in round 1 (round 0 = first attempt)
Prover:      gpt-6-astra
Setup:       GPT-6 Astra, which part of Lean feedback makes repair work: after a shared first attempt (E0), V = full error messages, Z = line numbers only, B = only "Lean rejected this proof"
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
  letI := hκ
  refine iInf_le_of_le
    (κ ∘ₖ Kernel.deterministic Prod.fst measurable_fst) ?_
  refine iInf_le_of_le inferInstance ?_
  have h : Kernel.deterministic Prod.fst measurable_fst ∘ₖ (P ⊗ₖ η) = P := by
    simpa [Kernel.deterministic_comp_eq_map, Kernel.fst] using
      Kernel.fst_compProd P η
  simp only [avgRisk, Kernel.comp_assoc, h]
  exact iSup_le fun θ => le_iSup (fun θ => ∫⁻ y, ℓ θ y ∂(κ ∘ₖ P) θ) θ
