/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     ModuleCat.depth_uliftFunctor_obj
Source:      Mathlib @ a02a63c2, Mathlib/RingTheory/Depth/Basic.lean, line 388
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  A1-astra, arm RT, verified in round 0 (round 0 = first attempt)
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

lemma ModuleCat.depth_uliftFunctor_obj [Small.{max v w} R] (N M : ModuleCat.{v} R) :
    ((ModuleCat.uliftFunctor.{w} R).obj N).depth ((ModuleCat.uliftFunctor.{w} R).obj M) =
    N.depth M := by
  classical
  simp only [ModuleCat.depth]
  congr 1
  ext n
  exact forall₂_congr fun i _ ↦
    (Equiv.ofBijective _
      ((ModuleCat.uliftFunctor.{w} R).mapExt_bijective_of_preservesProjectiveObjects
        N M i)).subsingleton_congr.symm
