/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     ExteriorAlgebra.baseChangeEquivForward_rightInverse
Source:      Mathlib @ a02a63c2, Mathlib/LinearAlgebra/ExteriorAlgebra/BaseChange.lean, line 81
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  O5-repair-sonnet, arm A, attempt 1, verified in round 0 (round 0 = first attempt)
Prover:      claude-sonnet-5-5
Setup:       Sonnet 5.5: arm B = repair loop; arm A = independent attempts
Check:       the proof replaced the human proof in the Mathlib file above; Lean reported
             0 errors and no `sorry`; sorry/admit/native_decide/search tactics were rejected.
-/

-- (context: the Mathlib file above this declaration)
lemma baseChangeEquivForward_rightInverse :
    (baseChangeEquivForward R M S).comp (baseChangeExteriorAlgebraToTensor R M S) =
      AlgHom.id S _ := by
  apply ExteriorAlgebra.hom_ext
  refine LinearMap.ext fun x => ?_
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul s m =>
    simp [baseChangeExteriorAlgebraToTensor, baseChangeEquivForward,
      baseChangeEquivForwardAux]
    all_goals
      (rw [← Algebra.smul_def, ← map_smul]
       simp [TensorProduct.smul_tmul'])
  | add x y hx hy =>
    rw [map_add, map_add, hx, hy]
