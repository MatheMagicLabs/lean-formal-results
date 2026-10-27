/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     ExteriorAlgebra.baseChangeι_sq_zero
Source:      Mathlib @ a02a63c2, Mathlib/LinearAlgebra/ExteriorAlgebra/BaseChange.lean, line 51
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  A2-astra-effort-low, arm R, verified in round 2 (round 0 = first attempt)
Prover:      gpt-6-astra
Setup:       GPT-6 Astra, reasoning effort low (arms R, N0)
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
    have h : ι R (m + n) * ι R (m + n) = 0 :=
      ι_sq_zero (m + n)
    simpa only [map_add, add_mul, mul_add, ι_sq_zero, zero_add,
      add_zero, add_comm] using h
  have hanti (u v : S ⊗[R] M) :
      baseChangeι R M S u * baseChangeι R M S v +
        baseChangeι R M S v * baseChangeι R M S u = 0 := by
    induction u using TensorProduct.induction_on with
    | zero => simp
    | tmul s m =>
        induction v using TensorProduct.induction_on with
        | zero => simp
        | tmul t n =>
            simp [baseChangeι, Algebra.TensorProduct.tmul_mul_tmul,
              mul_comm, ← TensorProduct.tmul_add, hι]
        | add v w hv hw =>
            simp only [map_add, mul_add, add_mul]
            calc
              _ = (baseChangeι R M S (s ⊗ₜ[R] m) * baseChangeι R M S v +
                    baseChangeι R M S v * baseChangeι R M S (s ⊗ₜ[R] m)) +
                  (baseChangeι R M S (s ⊗ₜ[R] m) * baseChangeι R M S w +
                    baseChangeι R M S w * baseChangeι R M S (s ⊗ₜ[R] m)) := by abel
              _ = 0 := by rw [hv, hw, add_zero]
    | add u w hu hw =>
        simp only [map_add, mul_add, add_mul]
        calc
          _ = (baseChangeι R M S u * baseChangeι R M S v +
                baseChangeι R M S v * baseChangeι R M S u) +
              (baseChangeι R M S w * baseChangeι R M S v +
                baseChangeι R M S v * baseChangeι R M S w) := by abel
          _ = 0 := by rw [hu, hw, add_zero]
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul s m =>
      simp [baseChangeι, Algebra.TensorProduct.tmul_mul_tmul]
  | add u v hu hv =>
      simp only [map_add, add_mul, mul_add]
      calc
        _ = baseChangeι R M S u * baseChangeι R M S u +
            (baseChangeι R M S u * baseChangeι R M S v +
              baseChangeι R M S v * baseChangeι R M S u) +
            baseChangeι R M S v * baseChangeι R M S v := by abel
        _ = 0 := by rw [hu, hv, hanti, add_zero, add_zero]
