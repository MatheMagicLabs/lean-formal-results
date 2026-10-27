/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     Algebra.Etale.of_etale_tensorProduct_of_faithfullyFlat
Source:      Mathlib @ d0a050ad6, Mathlib/RingTheory/Etale/Descent.lean, line 78 (group DRIFT)
Experiment:  UE1-deepseek-8-samples, arm sample 5, single attempt
Prover:      DeepSeek-Prover-V2-7B (4-bit)
Setup:       DeepSeek-Prover-V2-7B (4-bit, local), 8 independent samples per theorem, no Lean feedback;
             160 theorems: 80 DRIFT (human proof cites a lemma added after the 2025-05 snapshot) and 80 STABLE
Check:       the proof replaced the human proof in the Mathlib file above; Lean reported
             0 errors and no `sorry`.
-/

-- (context: the Mathlib file above this declaration)
lemma Etale.of_etale_tensorProduct_of_faithfullyFlat [Etale T (T ⊗[R] S)] :
    Etale R S := by
  have : Algebra.FinitePresentation R S := .of_finitePresentation_tensorProduct_of_faithfullyFlat T
  refine ⟨?_, .of_finitePresentation_tensorProduct_of_faithfullyFlat T⟩
  rw [formallyEtale_iff]
  constructor
  · have : FormallyUnramified T (T ⊗[R] S) := .of_formallyUnramified_tensorProduct_of_faithfullyFlat T
    have : FormallyUnramified R S := .of_formallyUnramified_tensorProduct_of_faithfullyFlat T
    exact?
  · have : Subsingleton (T ⊗[R] H1Cotangent R S) := (tensorH1CotangentOfFlat R S T).subsingleton
    exact?
