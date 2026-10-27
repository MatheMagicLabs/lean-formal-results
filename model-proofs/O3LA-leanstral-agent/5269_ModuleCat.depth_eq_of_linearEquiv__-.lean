/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     ModuleCat.depth_eq_of_linearEquiv
Source:      Mathlib @ a02a63c2, Mathlib/RingTheory/Depth/Basic.lean, line 402
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  O3LA-leanstral-agent, arm -, verified in final
Prover:      labs-leanstral-1-5
Setup:       Leanstral 1.5 as a tool-using agent (Mistral Vibe)
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
  let Lvw := ModuleCat.uliftFunctor.{w} R
  let Lwv := ModuleCat.uliftFunctor.{v} R
  let eN' : ULift.{w} N ≃ₗ[R] ULift.{v} N' :=
    (ULift.moduleEquiv (R := R) (M := N)).trans
      (eN.trans (ULift.moduleEquiv (R := R) (M := N')).symm)
  let eM' : ULift.{w} M ≃ₗ[R] ULift.{v} M' :=
    (ULift.moduleEquiv (R := R) (M := M)).trans
      (eM.trans (ULift.moduleEquiv (R := R) (M := M')).symm)
  have hN : Lvw.obj (ModuleCat.of R N) ≅ Lwv.obj (ModuleCat.of R N') :=
    eN'.toModuleIso
  have hM : Lvw.obj (ModuleCat.of R M) ≅ Lwv.obj (ModuleCat.of R M') :=
    eM'.toModuleIso
  calc
    (ModuleCat.of R N).depth (ModuleCat.of R M) =
      (Lvw.obj (ModuleCat.of R N)).depth (Lvw.obj (ModuleCat.of R M)) := by
      symm; apply ModuleCat.depth_uliftFunctor_obj
    _ = (Lwv.obj (ModuleCat.of R N')).depth (Lwv.obj (ModuleCat.of R M')) := by
      rw [depth_eq_of_iso_left (Lvw.obj (ModuleCat.of R M)) hN,
        depth_eq_of_iso_right (Lwv.obj (ModuleCat.of R N')) hM]
    _ = (ModuleCat.of R N').depth (ModuleCat.of R M') := by
      apply ModuleCat.depth_uliftFunctor_obj
