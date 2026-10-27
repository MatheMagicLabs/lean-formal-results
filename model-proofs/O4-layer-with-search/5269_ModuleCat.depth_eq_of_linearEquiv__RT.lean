/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     ModuleCat.depth_eq_of_linearEquiv
Source:      Mathlib @ a02a63c2, Mathlib/RingTheory/Depth/Basic.lean, line 402
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  O4-layer-with-search, arm RT, verified in round 1 (round 0 = first attempt)
Prover:      claude-opus-5-5
Setup:       Opus 5.5 with repair loop, lemma layer and name search (arm RT)
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
variable [Small.{w} R] {N M : Type v} {N' M' : Type w}

lemma ModuleCat.depth_eq_of_linearEquiv (eN : N ≃ₗ[R] N') (eM : M ≃ₗ[R] M') :
    (ModuleCat.of R N).depth (ModuleCat.of R M) =
      (ModuleCat.of R N').depth (ModuleCat.of R M') := by
  haveI : Small.{max v w} R := small_lift R
  haveI : Small.{max w v} R := small_lift R
  have h1 : ((ModuleCat.uliftFunctor.{w} R).obj (ModuleCat.of R N)).depth
      ((ModuleCat.uliftFunctor.{w} R).obj (ModuleCat.of R M)) =
      (ModuleCat.of R N).depth (ModuleCat.of R M) :=
    ModuleCat.depth_uliftFunctor_obj _ _
  have h2 : ((ModuleCat.uliftFunctor.{v} R).obj (ModuleCat.of R N')).depth
      ((ModuleCat.uliftFunctor.{v} R).obj (ModuleCat.of R M')) =
      (ModuleCat.of R N').depth (ModuleCat.of R M') :=
    ModuleCat.depth_uliftFunctor_obj _ _
  have e1 : (ModuleCat.uliftFunctor.{w} R).obj (ModuleCat.of R N) ≅
      (ModuleCat.uliftFunctor.{v} R).obj (ModuleCat.of R N') :=
    LinearEquiv.toModuleIso
      (ULift.moduleEquiv.trans (eN.trans ULift.moduleEquiv.symm))
  have e2 : (ModuleCat.uliftFunctor.{w} R).obj (ModuleCat.of R M) ≅
      (ModuleCat.uliftFunctor.{v} R).obj (ModuleCat.of R M') :=
    LinearEquiv.toModuleIso
      (ULift.moduleEquiv.trans (eM.trans ULift.moduleEquiv.symm))
  exact h1.symm.trans ((ModuleCat.depth_eq_of_iso_left _ e1).trans
    ((ModuleCat.depth_eq_of_iso_right _ e2).trans h2))
