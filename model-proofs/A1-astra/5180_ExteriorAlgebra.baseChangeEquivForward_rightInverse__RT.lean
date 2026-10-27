/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     ExteriorAlgebra.baseChangeEquivForward_rightInverse
Source:      Mathlib @ a02a63c2, Mathlib/LinearAlgebra/ExteriorAlgebra/BaseChange.lean, line 81
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  A1-astra, arm RT, verified in round 0 (round 0 = first attempt)
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

lemma baseChangeEquivForward_rightInverse :
    (baseChangeEquivForward R M S).comp (baseChangeExteriorAlgebraToTensor R M S) =
      AlgHom.id S _ := by
  apply ExteriorAlgebra.hom_ext
  apply LinearMap.ext
  intro x
  change baseChangeEquivForward R M S
    (baseChangeExteriorAlgebraToTensor R M S (ι S x)) = ι S x
  refine TensorProduct.inductionOn x ?_ ?_
  · intro s m
    have h : s ⊗ₜ[R] m = s • (1 ⊗ₜ[R] m) := by
      simp [TensorProduct.smul_tmul']
    rw [h]
    simp [baseChangeEquivForward, baseChangeEquivForwardAux,
      baseChangeExteriorAlgebraToTensor, baseChangeι]
  · intro x y hx hy
    simp only [map_add, hx, hy]
