/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     ExteriorAlgebra.baseChangeEquivForward_rightInverse
Source:      Mathlib @ a02a63c2, Mathlib/LinearAlgebra/ExteriorAlgebra/BaseChange.lean, line 81
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  O3-lemma-layer, arm R, verified in round 1 (round 0 = first attempt)
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

lemma baseChangeEquivForward_rightInverse :
    (baseChangeEquivForward R M S).comp (baseChangeExteriorAlgebraToTensor R M S) =
      AlgHom.id S _ := by
  apply ExteriorAlgebra.hom_ext
  apply TensorProduct.AlgebraTensorModule.ext
  intro s m
  simp [baseChangeEquivForward, baseChangeExteriorAlgebraToTensor,
    Algebra.TensorProduct.lift_tmul, baseChangeEquivForwardAux]
  first
  | done
  | (rw [Algebra.ofId_apply, ← Algebra.smul_def, ← map_smul, TensorProduct.smul_tmul',
      smul_eq_mul, mul_one])
  | (rw [← Algebra.smul_def, ← map_smul, TensorProduct.smul_tmul', smul_eq_mul, mul_one])
  | (simp only [Algebra.ofId_apply, ← Algebra.smul_def, ← map_smul, TensorProduct.smul_tmul',
      smul_eq_mul, mul_one, ExteriorAlgebra.ι_apply])
