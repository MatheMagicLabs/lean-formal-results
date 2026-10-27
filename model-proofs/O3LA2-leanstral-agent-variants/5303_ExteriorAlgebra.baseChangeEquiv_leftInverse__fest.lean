/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     ExteriorAlgebra.baseChangeEquiv_leftInverse
Source:      Mathlib @ a02a63c2, Mathlib/LinearAlgebra/ExteriorAlgebra/BaseChange.lean, line 75
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  O3LA2-leanstral-agent-variants, arm fest, verified in final
Prover:      labs-leanstral-1-5
Setup:       Leanstral 1.5 agent on the 29 theorems O3LA left open: neu = fresh restart, fest = fixed instruction, staffel = staged budget
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
  refine Algebra.TensorProduct.ext ?_ ?_
  · ext s
  · -- f (g (1 ⊗ₜ y)) = 1 ⊗ₜ y
    have h : ((baseChangeExteriorAlgebraToTensor R M S).restrictScalars R).comp
        (baseChangeEquivForwardAux R M S) =
        (Algebra.TensorProduct.includeRight (A := S) (B := ExteriorAlgebra R M)) := by
      apply ExteriorAlgebra.hom_ext
      ext m
      simp [baseChangeExteriorAlgebraToTensor, baseChangeEquivForwardAux, baseChangeι,
        ExteriorAlgebra.lift_ι_apply, ExteriorAlgebra.baseChangeι,
        Algebra.TensorProduct.lift_tmul]
    ext y
    simpa [baseChangeExteriorAlgebraToTensor, baseChangeEquivForward, baseChangeEquivForwardAux,
      Algebra.TensorProduct.lift_tmul] using congrArg (fun f => f y) h
