/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     ExteriorAlgebra.baseChangeEquiv_leftInverse
Source:      Mathlib @ a02a63c2, Mathlib/LinearAlgebra/ExteriorAlgebra/BaseChange.lean, line 75
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  O2-repair-vs-resample, arm A, attempt 3, verified in round 0 (round 0 = first attempt)
Prover:      claude-opus-5-5
Setup:       Opus 5.5: arm B = one attempt plus up to 3 repair rounds with Lean error messages; arm A = 4 independent attempts (attempt k)
Check:       the proof replaced the human proof in the Mathlib file above; Lean reported
             0 errors and no `sorry`; sorry/admit/native_decide/search tactics were rejected.
-/

-- (context: the Mathlib file above this declaration)
lemma baseChangeEquiv_leftInverse :
    (baseChangeExteriorAlgebraToTensor R M S).comp (baseChangeEquivForward R M S) =
      AlgHom.id S _ := by
  refine Algebra.TensorProduct.ext ?_ ?_
  · first
      | exact Subsingleton.elim _ _
      | exact Algebra.ext_id _ _ _
      | (ext; simp)
  · apply ExteriorAlgebra.hom_ext
    apply LinearMap.ext
    intro m
    simp [baseChangeEquivForward, baseChangeEquivForwardAux,
      baseChangeExteriorAlgebraToTensor]
