/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     ModuleCat.depth_uliftFunctor_obj
Source:      Mathlib @ a02a63c2, Mathlib/RingTheory/Depth/Basic.lean, line 388
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  O4-layer-with-search, arm RT, verified in round 0 (round 0 = first attempt)
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

lemma ModuleCat.depth_uliftFunctor_obj [Small.{max v w} R] (N M : ModuleCat.{v} R) :
    ((ModuleCat.uliftFunctor.{w} R).obj N).depth ((ModuleCat.uliftFunctor.{w} R).obj M) =
    N.depth M := by
  have h : ∀ i : ℕ, Subsingleton (Ext ((ModuleCat.uliftFunctor.{w} R).obj N)
      ((ModuleCat.uliftFunctor.{w} R).obj M) i) ↔ Subsingleton (Ext N M i) := fun i =>
    (Equiv.ofBijective _
      ((ModuleCat.uliftFunctor.{w} R).mapExt_bijective_of_preservesProjectiveObjects
        N M i)).subsingleton_congr.symm
  simp only [ModuleCat.depth_eq_sSup_lt_top, h]
