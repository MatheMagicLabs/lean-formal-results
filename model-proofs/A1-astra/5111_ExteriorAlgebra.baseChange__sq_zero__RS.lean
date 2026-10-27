/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     ExteriorAlgebra.baseChangeι_sq_zero
Source:      Mathlib @ a02a63c2, Mathlib/LinearAlgebra/ExteriorAlgebra/BaseChange.lean, line 51
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  A1-astra, arm RS, verified in round 1 (round 0 = first attempt)
Prover:      gpt-6-astra
Setup:       GPT-6 Astra (Codex, effort medium): R = proof plus up to 3 repair rounds with Lean errors; RS = R plus lemma layer; RT = R with read-only Mathlib sources to search; N0-N3 = independent attempts
Check:       the proof replaced the human proof in the Mathlib file above; Lean reported
             0 errors and no `sorry`; sorry/admit/native_decide/search tactics were rejected.
-/

noncomputable section
variable (R : Type*) [CommRing R] (M : Type*) [AddCommGroup M] [Module R M]
variable (S : Type*) [CommRing S] [Algebra R S]
open TensorProduct
namespace ExteriorAlgebra

lemma baseChangeι_sq_zero (x : S ⊗[R] M) : baseChangeι R M S x * baseChangeι R M S x = 0 := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul s m =>
      simp [baseChangeι, Algebra.TensorProduct.tmul_mul_tmul, ι_sq_zero]
  | add x y hx hy =>
      rw [map_add]
      calc
        _ = baseChangeι R M S x * baseChangeι R M S x +
            (baseChangeι R M S x * baseChangeι R M S y +
              baseChangeι R M S y * baseChangeι R M S x) +
            baseChangeι R M S y * baseChangeι R M S y := by
              simp only [add_mul, mul_add, add_assoc, add_comm, add_left_comm]
        _ = 0 := by
          rw [hx, hy, baseChangeι_mul_add_swap]
          simp
