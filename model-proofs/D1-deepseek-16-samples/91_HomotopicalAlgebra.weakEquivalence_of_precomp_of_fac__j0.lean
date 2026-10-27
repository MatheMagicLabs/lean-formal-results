/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     HomotopicalAlgebra.weakEquivalence_of_precomp_of_fac
Source:      Mathlib @ d0a050ad6, Mathlib/AlgebraicTopology/ModelCategory/Instances.lean, line 97 (group STABLE)
Experiment:  D1-deepseek-16-samples, arm sample 0, single attempt
Prover:      DeepSeek-Prover-V2-7B (4-bit)
Setup:       DeepSeek-Prover-V2-7B (4-bit, local), 16 independent samples per theorem, no Lean feedback;
             160 theorems: 80 DRIFT (human proof cites a lemma added after the 2025-05 snapshot) and 80 STABLE
Check:       the proof replaced the human proof in the Mathlib file above; Lean reported
             0 errors and no `sorry`.
-/

-- (context: the Mathlib file above this declaration)
lemma weakEquivalence_of_precomp_of_fac (fac : f ≫ g = fg)
    [WeakEquivalence f] [WeakEquivalence fg] :
    WeakEquivalence g := by
  subst fac
  exact weakEquivalence_of_precomp f g
