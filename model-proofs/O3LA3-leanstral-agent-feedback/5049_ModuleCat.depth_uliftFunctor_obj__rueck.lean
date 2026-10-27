/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     ModuleCat.depth_uliftFunctor_obj
Source:      Mathlib @ a02a63c2, Mathlib/RingTheory/Depth/Basic.lean, line 388
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  O3LA3-leanstral-agent-feedback, arm rueck, verified in final
Prover:      labs-leanstral-1-5
Setup:       Leanstral 1.5 agent with goal-state feedback (arm rueck)
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
  set F := ModuleCat.uliftFunctor.{w} R
  have h_bijective (n : ℕ) : Function.Bijective (F.mapExtAddHom N M n) := by
    exact Functor.mapExt_bijective_of_preservesProjectiveObjects F N M n
  have hinj (n : ℕ) : Function.Injective (F.mapExtAddHom N M n) := (h_bijective n).injective
  have hsurj (n : ℕ) : Function.Surjective (F.mapExtAddHom N M n) := (h_bijective n).surjective
  apply le_antisymm
  · apply sSup_le
    intro n hn
    simp only [Set.mem_setOf_eq] at hn
    apply le_sSup
    simp only [Set.mem_setOf_eq]
    intro i hi
    haveI : Subsingleton (Ext (F.obj N) (F.obj M) i) := hn i hi
    exact (hinj i).subsingleton
  · apply sSup_le
    intro n hn
    simp only [Set.mem_setOf_eq] at hn
    apply le_sSup
    simp only [Set.mem_setOf_eq]
    intro i hi
    haveI : Subsingleton (Ext N M i) := hn i hi
    exact (hsurj i).subsingleton
