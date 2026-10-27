/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     ExteriorAlgebra.baseChangeι_mul_add_swap
Source:      Mathlib @ a02a63c2, Mathlib/LinearAlgebra/ExteriorAlgebra/BaseChange.lean, line 38
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  O2-repair-vs-resample, arm A, attempt 2, verified in round 0 (round 0 = first attempt)
Prover:      claude-opus-5-5
Setup:       Opus 5.5: arm B = one attempt plus up to 3 repair rounds with Lean error messages; arm A = 4 independent attempts (attempt k)
Check:       the proof replaced the human proof in the Mathlib file above; Lean reported
             0 errors and no `sorry`; sorry/admit/native_decide/search tactics were rejected.
-/

-- (context: the Mathlib file above this declaration)
lemma baseChangeι_mul_add_swap (x y : S ⊗[R] M) :
    baseChangeι R M S x * baseChangeι R M S y + baseChangeι R M S y * baseChangeι R M S x = 0 := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul s m =>
    induction y using TensorProduct.induction_on with
    | zero => simp
    | tmul t n =>
      simp only [baseChangeι, LinearMap.baseChange_tmul, Algebra.TensorProduct.tmul_mul_tmul]
      rw [mul_comm t s, ← tmul_add, ExteriorAlgebra.ι_add_mul_swap, tmul_zero]
    | add y z hy hz =>
      simp only [map_add, mul_add, add_mul]
      rw [add_add_add_comm, hy, hz, add_zero]
  | add x z hx hz =>
    simp only [map_add, mul_add, add_mul]
    rw [add_add_add_comm, hx, hz, add_zero]
