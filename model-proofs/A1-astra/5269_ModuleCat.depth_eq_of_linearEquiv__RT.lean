/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     ModuleCat.depth_eq_of_linearEquiv
Source:      Mathlib @ a02a63c2, Mathlib/RingTheory/Depth/Basic.lean, line 402
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  A1-astra, arm RT, verified in round 1 (round 0 = first attempt)
Prover:      gpt-6-astra
Setup:       GPT-6 Astra (Codex, effort medium): R = proof plus up to 3 repair rounds with Lean errors; RS = R plus lemma layer; RT = R with read-only Mathlib sources to search; N0-N3 = independent attempts
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
  letI : Small.{max v w} R := small_lift.{u, v, w} R
  let eN' : ULift.{w} N ≃ₗ[R] ULift.{v} N' :=
    (ULift.moduleEquiv.trans eN).trans ULift.moduleEquiv.symm
  let eM' : ULift.{w} M ≃ₗ[R] ULift.{v} M' :=
    (ULift.moduleEquiv.trans eM).trans ULift.moduleEquiv.symm
  calc
    (ModuleCat.of R N).depth (ModuleCat.of R M) =
        (ModuleCat.of R (ULift.{w} N)).depth
          (ModuleCat.of R (ULift.{w} M)) :=
      (ModuleCat.depth_uliftFunctor_obj.{v, u, w}
        (ModuleCat.of R N) (ModuleCat.of R M)).symm
    _ = (ModuleCat.of R (ULift.{v} N')).depth
          (ModuleCat.of R (ULift.{v} M')) := by
      rw [ModuleCat.depth_eq_of_iso_left _ eN'.toModuleIso,
        ModuleCat.depth_eq_of_iso_right _ eM'.toModuleIso]
    _ = (ModuleCat.of R N').depth (ModuleCat.of R M') :=
      ModuleCat.depth_uliftFunctor_obj.{w, u, v}
        (ModuleCat.of R N') (ModuleCat.of R M')
