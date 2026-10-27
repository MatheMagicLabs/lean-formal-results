/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     ModuleCat.depth_uliftFunctor_obj
Source:      Mathlib @ a02a63c2, Mathlib/RingTheory/Depth/Basic.lean, line 388
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

lemma ModuleCat.depth_uliftFunctor_obj [Small.{max v w} R] (N M : ModuleCat.{v} R) :
    ((ModuleCat.uliftFunctor.{w} R).obj N).depth ((ModuleCat.uliftFunctor.{w} R).obj M) =
    N.depth M := by
  rw [depth_eq_sSup_lt_top, depth_eq_sSup_lt_top]
  congr
  ext n
  constructor
  · rintro ⟨hn, h⟩
    refine ⟨hn, fun i hi ↦ ?_⟩
    have h_bijective := Functor.mapExt_bijective_of_preservesProjectiveObjects
      (ModuleCat.uliftFunctor.{w} R) N M i
    haveI : Subsingleton (Ext ((ModuleCat.uliftFunctor.{w} R).obj N)
      ((ModuleCat.uliftFunctor.{w} R).obj M) i) := h i hi
    exact h_bijective.injective.subsingleton
  · rintro ⟨hn, h⟩
    refine ⟨hn, fun i hi ↦ ?_⟩
    have h_bijective := Functor.mapExt_bijective_of_preservesProjectiveObjects
      (ModuleCat.uliftFunctor.{w} R) N M i
    haveI : Subsingleton (Ext N M i) := h i hi
    exact h_bijective.surjective.subsingleton
