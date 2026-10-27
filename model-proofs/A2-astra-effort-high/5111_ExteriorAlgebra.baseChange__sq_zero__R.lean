/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     ExteriorAlgebra.baseChangeι_sq_zero
Source:      Mathlib @ a02a63c2, Mathlib/LinearAlgebra/ExteriorAlgebra/BaseChange.lean, line 51
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  A2-astra-effort-high, arm R, verified in round 2 (round 0 = first attempt)
Prover:      gpt-6-astra
Setup:       GPT-6 Astra, reasoning effort high (arms R, N0)
Check:       the proof replaced the human proof in the Mathlib file above; Lean reported
             0 errors and no `sorry`; sorry/admit/native_decide/search tactics were rejected.
-/

noncomputable section
variable (R : Type*) [CommRing R] (M : Type*) [AddCommGroup M] [Module R M]
variable (S : Type*) [CommRing S] [Algebra R S]
open TensorProduct
namespace ExteriorAlgebra

lemma baseChangeι_sq_zero (x : S ⊗[R] M) : baseChangeι R M S x * baseChangeι R M S x = 0 := by
  have h (u v : S ⊗[R] M) :
      baseChangeι R M S u * baseChangeι R M S v +
        baseChangeι R M S v * baseChangeι R M S u = 0 := by
    induction u using TensorProduct.induction_on with
    | zero => simp
    | tmul s m =>
      induction v using TensorProduct.induction_on with
      | zero => simp
      | tmul t n =>
        have hsq :
            ι R (m + n) * ι R (m + n) = 0 :=
          ι_sq_zero (m + n)
        have hmn :
            ι R m * ι R n + ι R n * ι R m = 0 := by
          simpa [map_add, add_mul, mul_add] using hsq
        change
          (s ⊗ₜ[R] ι R m) * (t ⊗ₜ[R] ι R n) +
            (t ⊗ₜ[R] ι R n) * (s ⊗ₜ[R] ι R m) = 0
        simp only [Algebra.TensorProduct.tmul_mul_tmul]
        rw [mul_comm t s, ← TensorProduct.tmul_add, hmn]
        simp
      | add v w hv hw =>
        simpa only [map_add, add_mul, mul_add, add_assoc,
          add_left_comm, add_comm, add_zero] using
          congrArg₂ (· + ·) hv hw
    | add u w hu hw =>
      simpa only [map_add, add_mul, mul_add, add_assoc,
        add_left_comm, add_comm, add_zero] using
        congrArg₂ (· + ·) hu hw
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul s m =>
    change
      (s ⊗ₜ[R] ι R m) * (s ⊗ₜ[R] ι R m) = 0
    simp
  | add u v hu hv =>
    simpa only [map_add, add_mul, mul_add, add_assoc,
      add_left_comm, add_comm, add_zero] using
      congrArg₂ (· + ·) (congrArg₂ (· + ·) hu (h u v)) hv
