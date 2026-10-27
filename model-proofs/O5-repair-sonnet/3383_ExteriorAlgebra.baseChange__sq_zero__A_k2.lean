/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     ExteriorAlgebra.baseChangeι_sq_zero
Source:      Mathlib @ a02a63c2, Mathlib/LinearAlgebra/ExteriorAlgebra/BaseChange.lean, line 51
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  O5-repair-sonnet, arm A, attempt 2, verified in round 0 (round 0 = first attempt)
Prover:      claude-sonnet-5-5
Setup:       Sonnet 5.5: arm B = repair loop; arm A = independent attempts
Check:       the proof replaced the human proof in the Mathlib file above; Lean reported
             0 errors and no `sorry`; sorry/admit/native_decide/search tactics were rejected.
-/

-- (context: the Mathlib file above this declaration)
lemma baseChangeι_sq_zero (x : S ⊗[R] M) : baseChangeι R M S x * baseChangeι R M S x = 0 := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul s m => simp [Algebra.TensorProduct.tmul_mul_tmul]
  | add a b ha hb =>
    have h := baseChangeι_mul_add_swap R M S a b
    simp only [map_add, add_mul, mul_add]
    calc _ = (baseChangeι R M S a * baseChangeι R M S a)
          + (baseChangeι R M S a * baseChangeι R M S b
            + baseChangeι R M S b * baseChangeι R M S a)
          + (baseChangeι R M S b * baseChangeι R M S b) := by abel
      _ = 0 := by rw [ha, hb, h]; simp
