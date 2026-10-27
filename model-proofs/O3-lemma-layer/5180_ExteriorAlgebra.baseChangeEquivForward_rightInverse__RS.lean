/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     ExteriorAlgebra.baseChangeEquivForward_rightInverse
Source:      Mathlib @ a02a63c2, Mathlib/LinearAlgebra/ExteriorAlgebra/BaseChange.lean, line 81
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  O3-lemma-layer, arm RS, verified in round 2 (round 0 = first attempt)
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
  ext s m
  simp only [AlgHom.comp_toLinearMap, LinearMap.coe_comp, Function.comp_apply,
    AlgHom.toLinearMap_apply, AlgHom.coe_id, id_eq,
    TensorProduct.AlgebraTensorModule.curry_apply, TensorProduct.curry_apply,
    LinearMap.coe_restrictScalars, AlgHom.coe_comp] at *
  simp [baseChangeExteriorAlgebraToTensor]
  first
    | refine (Algebra.TensorProduct.lift_tmul _ _ _ _ _).trans ?_
    | (unfold baseChangeEquivForward; erw [Algebra.TensorProduct.lift_tmul])
  rw [map_one, one_mul]
  first
    | rfl
    | simp [baseChangeEquivForwardAux]
    | simp [baseChangeEquivForwardAux, ExteriorAlgebra.lift_ι_apply, CliffordAlgebra.lift_ι_apply]
    | (unfold baseChangeEquivForwardAux; simp)
