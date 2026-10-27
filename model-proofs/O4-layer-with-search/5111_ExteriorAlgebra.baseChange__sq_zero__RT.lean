/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     ExteriorAlgebra.baseChangeι_sq_zero
Source:      Mathlib @ a02a63c2, Mathlib/LinearAlgebra/ExteriorAlgebra/BaseChange.lean, line 51
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  O4-layer-with-search, arm RT, verified in round 0 (round 0 = first attempt)
Prover:      claude-opus-5-5
Setup:       Opus 5.5 with repair loop, lemma layer and name search (arm RT)
Check:       the proof replaced the human proof in the Mathlib file above; Lean reported
             0 errors and no `sorry`; sorry/admit/native_decide/search tactics were rejected.
-/

noncomputable section
variable (R : Type*) [CommRing R] (M : Type*) [AddCommGroup M] [Module R M]
variable (S : Type*) [CommRing S] [Algebra R S]
open TensorProduct
namespace ExteriorAlgebra

lemma baseChangeι_sq_zero (x : S ⊗[R] M) : baseChangeι R M S x * baseChangeι R M S x = 0 := by
  have ht : ∀ (s : S) (m : M), baseChangeι R M S (s ⊗ₜ m) = s ⊗ₜ ι R m := by
    intro s m
    first
      | rfl
      | simp [baseChangeι]
  have key : ∀ x y : S ⊗[R] M,
      baseChangeι R M S x * baseChangeι R M S y
        + baseChangeι R M S y * baseChangeι R M S x = 0 := by
    intro x y
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul s m =>
      induction y using TensorProduct.induction_on with
      | zero => simp
      | tmul t n =>
        rw [ht, ht, Algebra.TensorProduct.tmul_mul_tmul, Algebra.TensorProduct.tmul_mul_tmul,
          mul_comm t s, ← TensorProduct.tmul_add, ι_add_mul_swap, TensorProduct.tmul_zero]
      | add a b ha hb =>
        simp only [map_add, mul_add, add_mul]
        rw [add_add_add_comm, ha, hb, add_zero]
    | add a b ha hb =>
      simp only [map_add, mul_add, add_mul]
      rw [add_add_add_comm, ha, hb, add_zero]
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul s m =>
    rw [ht, Algebra.TensorProduct.tmul_mul_tmul, ι_sq_zero, TensorProduct.tmul_zero]
  | add a b ha hb =>
    have h := key a b
    simp only [map_add, mul_add, add_mul]
    rw [ha, hb, zero_add, add_zero, add_comm]
    exact h
