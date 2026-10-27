/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     ExteriorAlgebra.baseChangeEquivForward_rightInverse
Source:      Mathlib @ a02a63c2, Mathlib/LinearAlgebra/ExteriorAlgebra/BaseChange.lean, line 81
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

lemma baseChangeEquivForward_rightInverse :
    (baseChangeEquivForward R M S).comp (baseChangeExteriorAlgebraToTensor R M S) =
      AlgHom.id S _ := by
  apply ExteriorAlgebra.hom_ext
  apply TensorProduct.AlgebraTensorModule.curry_injective
  ext m
  simp [baseChangeExteriorAlgebraToTensor, baseChangeEquivForward, baseChangeι,
    baseChangeEquivForwardAux, mul_comm, mul_one]
