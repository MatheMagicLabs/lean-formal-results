/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     ExteriorAlgebra.baseChangeEquivForward_rightInverse
Source:      Mathlib @ a02a63c2, Mathlib/LinearAlgebra/ExteriorAlgebra/BaseChange.lean, line 81
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  O5-repair-sonnet, arm B, verified in round 0 (round 0 = first attempt)
Prover:      claude-sonnet-5-5
Setup:       Sonnet 5.5: arm B = repair loop; arm A = independent attempts
Check:       the proof replaced the human proof in the Mathlib file above; Lean reported
             0 errors and no `sorry`; sorry/admit/native_decide/search tactics were rejected.
-/

-- (context: the Mathlib file above this declaration)
lemma baseChangeEquivForward_rightInverse :
    (baseChangeEquivForward R M S).comp (baseChangeExteriorAlgebraToTensor R M S) =
      AlgHom.id S _ := by
  have key : ∀ x : S ⊗[R] M,
      (baseChangeEquivForward R M S) ((baseChangeExteriorAlgebraToTensor R M S)
        (ExteriorAlgebra.ι S x)) = ExteriorAlgebra.ι S x := by
    intro x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul s m =>
      have h1 : baseChangeExteriorAlgebraToTensor R M S (ExteriorAlgebra.ι S (s ⊗ₜ[R] m))
          = s ⊗ₜ[R] ExteriorAlgebra.ι R m := by
        simp [baseChangeExteriorAlgebraToTensor]
      have h2 : baseChangeEquivForward R M S (s ⊗ₜ[R] ExteriorAlgebra.ι R m)
          = algebraMap S _ s * ExteriorAlgebra.ι S ((1 : S) ⊗ₜ[R] m) := by
        simp [baseChangeEquivForward, baseChangeEquivForwardAux]
      rw [h1, h2, ← Algebra.smul_def, ← map_smul, TensorProduct.smul_tmul', smul_eq_mul,
        mul_one]
    | add x y hx hy =>
      rw [map_add, map_add, map_add, hx, hy]
  apply ExteriorAlgebra.hom_ext
  exact LinearMap.ext fun x => key x
