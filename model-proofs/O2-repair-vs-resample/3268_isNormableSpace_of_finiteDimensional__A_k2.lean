/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     isNormableSpace_of_finiteDimensional
Source:      Mathlib @ a02a63c2, Mathlib/Topology/Algebra/Module/FiniteDimension.lean, line 614
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  O2-repair-vs-resample, arm A, attempt 2, verified in round 0 (round 0 = first attempt)
Prover:      claude-opus-5-5
Setup:       Opus 5.5: arm B = one attempt plus up to 3 repair rounds with Lean error messages; arm A = 4 independent attempts (attempt k)
Check:       the proof replaced the human proof in the Mathlib file above; Lean reported
             0 errors and no `sorry`; sorry/admit/native_decide/search tactics were rejected.
-/

-- (context: the Mathlib file above this declaration)
theorem isNormableSpace_of_finiteDimensional [FiniteDimensional 𝕜 E] : IsNormableSpace 𝕜 E := by
  haveI : IsNormableSpace 𝕜 (SeparationQuotient E) :=
    isNormableSpace_of_t2Space_finiteDimensional (SeparationQuotient E)
  first
  | exact IsNormableSpace.induced (SeparationQuotient.mkCLM 𝕜 E) SeparationQuotient.isInducing_mk
  | exact (SeparationQuotient.isInducing_mk).isNormableSpace (SeparationQuotient.mkCLM 𝕜 E)
  | exact SeparationQuotient.isInducing_mk.isNormableSpace
      (f := (SeparationQuotient.mkCLM 𝕜 E).toLinearMap)
  | exact IsNormableSpace.of_isInducing (SeparationQuotient.mkCLM 𝕜 E)
      SeparationQuotient.isInducing_mk
  | exact (SeparationQuotient.mkCLM 𝕜 E).isNormableSpace_of_isInducing
      SeparationQuotient.isInducing_mk
  | exact IsNormableSpace.comap (SeparationQuotient.mkCLM 𝕜 E) SeparationQuotient.isInducing_mk
