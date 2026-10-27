/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     ExteriorAlgebra.baseChangeEquiv_leftInverse
Source:      Mathlib @ a02a63c2, Mathlib/LinearAlgebra/ExteriorAlgebra/BaseChange.lean, line 75
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  O3-lemma-layer, arm RS, verified in round 1 (round 0 = first attempt)
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

lemma baseChangeEquiv_leftInverse :
    (baseChangeExteriorAlgebraToTensor R M S).comp (baseChangeEquivForward R M S) =
      AlgHom.id S _ := by
  ext x
  change baseChangeExteriorAlgebraToTensor R M S
      (baseChangeEquivForward R M S ((1 : S) ⊗ₜ[R] ExteriorAlgebra.ι R x)) =
    (1 : S) ⊗ₜ[R] ExteriorAlgebra.ι R x
  simp [baseChangeEquivForward, baseChangeEquivForwardAux,
    baseChangeExteriorAlgebraToTensor, baseChangeι,
    Algebra.TensorProduct.lift_tmul, ExteriorAlgebra.lift_ι_apply]
