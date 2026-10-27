/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     isNormableSpace_of_finiteDimensional
Source:      Mathlib @ a02a63c2, Mathlib/Topology/Algebra/Module/FiniteDimension.lean, line 614
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  O5-repair-sonnet, arm B, verified in round 1 (round 0 = first attempt)
Prover:      claude-sonnet-5-5
Setup:       Sonnet 5.5: arm B = repair loop; arm A = independent attempts
Check:       the proof replaced the human proof in the Mathlib file above; Lean reported
             0 errors and no `sorry`; sorry/admit/native_decide/search tactics were rejected.
-/

-- (context: the Mathlib file above this declaration)
theorem isNormableSpace_of_finiteDimensional [FiniteDimensional 𝕜 E] : IsNormableSpace 𝕜 E := by
  have h := isNormableSpace_of_t2Space_finiteDimensional (𝕜 := 𝕜) (SeparationQuotient E)
  have hi : IsInducing (SeparationQuotient.mkCLM 𝕜 E) := SeparationQuotient.isInducing_mk
  first
  | exact hi.isNormableSpace (𝕜 := 𝕜)
  | exact Topology.IsInducing.isNormableSpace (𝕜 := 𝕜) hi
  | exact IsNormableSpace.of_isInducing (SeparationQuotient.mkCLM 𝕜 E).toLinearMap hi
  | exact IsNormableSpace.of_isInducing (𝕜 := 𝕜) hi
  | exact IsNormableSpace.of_isInducing' (𝕜 := 𝕜) hi
  | exact IsNormableSpace.induced (SeparationQuotient.mkCLM 𝕜 E) hi
  | exact IsNormableSpace.induced (SeparationQuotient.mkCLM 𝕜 E).toLinearMap hi
  | exact IsNormableSpace.of_continuousLinearMap_isInducing (SeparationQuotient.mkCLM 𝕜 E) hi
  | exact (SeparationQuotient.mkCLM 𝕜 E).isNormableSpace_of_isInducing hi
  | exact (SeparationQuotient.mkCLM 𝕜 E).isNormableSpace hi
  | exact hi.isNormableSpace (SeparationQuotient.mkCLM 𝕜 E)
  | exact h.of_isInducing (SeparationQuotient.mkCLM 𝕜 E) hi
