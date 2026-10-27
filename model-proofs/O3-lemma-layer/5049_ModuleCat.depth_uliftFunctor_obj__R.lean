/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     ModuleCat.depth_uliftFunctor_obj
Source:      Mathlib @ a02a63c2, Mathlib/RingTheory/Depth/Basic.lean, line 388
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  O3-lemma-layer, arm R, verified in round 2 (round 0 = first attempt)
Prover:      claude-opus-5-5
Setup:       Opus 5.5 with repair loop: arm R = repair only; arm RS = repair plus the Lean-checked lemma layer
Check:       the proof replaced the human proof in the Mathlib file above; Lean reported
             0 errors and no `sorry`; sorry/admit/native_decide/search tactics were rejected.
-/

open IsLocalRing LinearMap Module
universe v u
open RingTheory.Sequence Ideal CategoryTheory Abelian Limits Pointwise ModuleCat IsSMulRegular
variable {R : Type u} [CommRing R] [Small.{v} R]
section depth
namespace ModuleCat
open Classical in
end ModuleCat
section
universe w

lemma ModuleCat.depth_uliftFunctor_obj [Small.{max v w} R] (N M : ModuleCat.{v} R) :
    ((ModuleCat.uliftFunctor.{w} R).obj N).depth ((ModuleCat.uliftFunctor.{w} R).obj M) =
    N.depth M := by
  simp only [ModuleCat.depth]
  congr! 3 with n
  refine forall_congr' fun i => forall_congr' fun _ => ?_
  try apply propext
  first
  | exact ((ModuleCat.uliftFunctor.{w} R).mapExtAddEquiv N M i).subsingleton_congr
  | exact ((ModuleCat.uliftFunctor R).mapExtAddEquiv N M i).subsingleton_congr
  | exact (ModuleCat.extULiftLinearEquiv.{w} N M i).toEquiv.subsingleton_congr
  | exact (ModuleCat.extULiftLinearEquiv N M i).toEquiv.subsingleton_congr
  | exact (ModuleCat.uliftFunctorExtLinearEquiv.{w} N M i).toEquiv.subsingleton_congr
  | (constructor
     · intro h
       exact ((ModuleCat.uliftFunctor.{w} R).mapExt_bijective_of_fullyFaithful N M i).1.subsingleton
     · intro h
       exact ((ModuleCat.uliftFunctor.{w} R).mapExt_bijective_of_fullyFaithful N M i).2.subsingleton)
  | (constructor
     · intro h
       exact ((ModuleCat.uliftFunctor.{w} R).mapExt_bijective_of_preservesProjectiveObjects
         N M i).1.subsingleton
     · intro h
       exact ((ModuleCat.uliftFunctor.{w} R).mapExt_bijective_of_preservesProjectiveObjects
         N M i).2.subsingleton)
  | (constructor
     · intro h
       exact ((ModuleCat.uliftFunctor.{w} R).mapExt_bijective N M i).1.subsingleton
     · intro h
       exact ((ModuleCat.uliftFunctor.{w} R).mapExt_bijective N M i).2.subsingleton)
