/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     ExteriorAlgebra.baseChangeι_sq_zero
Source:      Mathlib @ a02a63c2, Mathlib/LinearAlgebra/ExteriorAlgebra/BaseChange.lean, line 51
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  O3-lemma-layer, arm R, verified in round 0 (round 0 = first attempt)
Prover:      claude-opus-5-5
Setup:       Opus 5.5 with repair loop: arm R = repair only; arm RS = repair plus the Lean-checked lemma layer
Check:       the proof replaced the human proof in the Mathlib file above; Lean reported
             0 errors and no `sorry`; sorry/admit/native_decide/search tactics were rejected.
-/

noncomputable section
variable (R : Type*) [CommRing R] (M : Type*) [AddCommGroup M] [Module R M]
variable (S : Type*) [CommRing S] [Algebra R S]
open TensorProduct
namespace ExteriorAlgebra

lemma baseChangeι_sq_zero (x : S ⊗[R] M) : baseChangeι R M S x * baseChangeι R M S x = 0 := by
  have key : ∀ (s t : S) (m n : M),
      baseChangeι R M S (s ⊗ₜ m) * baseChangeι R M S (t ⊗ₜ n) +
        baseChangeι R M S (t ⊗ₜ n) * baseChangeι R M S (s ⊗ₜ m) = 0 := by
    intro s t m n
    simp [baseChangeι, Algebra.TensorProduct.tmul_mul_tmul, mul_comm t s,
      ← TensorProduct.tmul_add, ι_add_mul_swap]
  have anti : ∀ x y : S ⊗[R] M,
      baseChangeι R M S x * baseChangeι R M S y +
        baseChangeι R M S y * baseChangeι R M S x = 0 := by
    intro x y
    induction x using TensorProduct.induction_on with
    | zero => simp
    | add a b ha hb =>
      calc _ = (baseChangeι R M S a * baseChangeι R M S y +
            baseChangeι R M S y * baseChangeι R M S a) +
            (baseChangeι R M S b * baseChangeι R M S y +
            baseChangeι R M S y * baseChangeι R M S b) := by
            rw [map_add, add_mul, mul_add]; abel
        _ = 0 := by rw [ha, hb, add_zero]
    | tmul s m =>
      induction y using TensorProduct.induction_on with
      | zero => simp
      | add a b ha hb =>
        calc _ = (baseChangeι R M S (s ⊗ₜ m) * baseChangeι R M S a +
              baseChangeι R M S a * baseChangeι R M S (s ⊗ₜ m)) +
              (baseChangeι R M S (s ⊗ₜ m) * baseChangeι R M S b +
              baseChangeι R M S b * baseChangeι R M S (s ⊗ₜ m)) := by
              rw [map_add, add_mul, mul_add]; abel
          _ = 0 := by rw [ha, hb, add_zero]
      | tmul t n => exact key s t m n
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul s m =>
    simp [baseChangeι, Algebra.TensorProduct.tmul_mul_tmul]
  | add a b ha hb =>
    rw [map_add, add_mul, mul_add, mul_add, ha, hb, zero_add, add_zero]
    exact anti a b
