/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     ExteriorAlgebra.baseChangeι_sq_zero
Source:      Mathlib @ a02a63c2, Mathlib/LinearAlgebra/ExteriorAlgebra/BaseChange.lean, line 51
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  E1-repair-decomposition, arm V, verified in round 2 (round 0 = first attempt)
Prover:      gpt-6-astra
Setup:       GPT-6 Astra, which part of Lean feedback makes repair work: after a shared first attempt (E0), V = full error messages, Z = line numbers only, B = only "Lean rejected this proof"
Check:       the proof replaced the human proof in the Mathlib file above; Lean reported
             0 errors and no `sorry`; sorry/admit/native_decide/search tactics were rejected.
-/

noncomputable section
variable (R : Type*) [CommRing R] (M : Type*) [AddCommGroup M] [Module R M]
variable (S : Type*) [CommRing S] [Algebra R S]
open TensorProduct
namespace ExteriorAlgebra

lemma baseChangeι_sq_zero (x : S ⊗[R] M) : baseChangeι R M S x * baseChangeι R M S x = 0 := by
  have hι (m n : M) :
      ι R m * ι R n + ι R n * ι R m = 0 := by
    have h : ι R (m + n) * ι R (m + n) = 0 := ι_sq_zero (m + n)
    simpa only [map_add, add_mul, mul_add, ι_sq_zero, zero_add, add_zero,
      add_comm] using h
  let f := baseChangeι R M S
  have hanti (u v : S ⊗[R] M) : f u * f v + f v * f u = 0 := by
    induction u using TensorProduct.induction_on with
    | zero => simp [f]
    | tmul s m =>
        induction v using TensorProduct.induction_on with
        | zero => simp [f]
        | tmul t n =>
            simpa [f, baseChangeι, mul_comm t s, ← TensorProduct.tmul_add] using
              congrArg
                (fun z : ExteriorAlgebra R M => (s * t) ⊗ₜ[R] z)
                (hι m n)
        | add v w hv hw =>
            calc
              _ = (f (s ⊗ₜ[R] m) * f v + f v * f (s ⊗ₜ[R] m)) +
                  (f (s ⊗ₜ[R] m) * f w + f w * f (s ⊗ₜ[R] m)) := by
                    simp only [map_add, mul_add, add_mul]
                    abel
              _ = 0 := by rw [hv, hw, add_zero]
    | add u w hu hw =>
        calc
          _ = (f u * f v + f v * f u) +
              (f w * f v + f v * f w) := by
                simp only [map_add, mul_add, add_mul]
                abel
          _ = 0 := by rw [hu, hw, add_zero]
  change f x * f x = 0
  induction x using TensorProduct.induction_on with
  | zero => simp [f]
  | tmul s m => simp [f, baseChangeι, ι_sq_zero]
  | add u v hu hv =>
      calc
        _ = f u * f u + (f u * f v + f v * f u) + f v * f v := by
          simp only [map_add, mul_add, add_mul]
          abel
        _ = 0 := by rw [hu, hv, hanti u v]; simp
