/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     ModuleCat.depth_uliftFunctor_obj
Source:      Mathlib @ a02a63c2, Mathlib/RingTheory/Depth/Basic.lean, line 388
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  O2-repair-vs-resample, arm A, attempt 1, verified in round 0 (round 0 = first attempt)
Prover:      claude-opus-5-5
Setup:       Opus 5.5: arm B = one attempt plus up to 3 repair rounds with Lean error messages; arm A = 4 independent attempts (attempt k)
Check:       the proof replaced the human proof in the Mathlib file above; Lean reported
             0 errors and no `sorry`; sorry/admit/native_decide/search tactics were rejected.
-/

-- (context: the Mathlib file above this declaration)
lemma ModuleCat.depth_uliftFunctor_obj [Small.{max v w} R] (N M : ModuleCat.{v} R) :
    ((ModuleCat.uliftFunctor.{w} R).obj N).depth ((ModuleCat.uliftFunctor.{w} R).obj M) =
    N.depth M := by
  have h : ∀ i : ℕ, Subsingleton (Ext ((ModuleCat.uliftFunctor.{w} R).obj N)
      ((ModuleCat.uliftFunctor.{w} R).obj M) i) ↔ Subsingleton (Ext N M i) := by
    intro i
    first
    | exact (Equiv.ofBijective _ ((ModuleCat.uliftFunctor.{w} R).mapExt_bijective_of_preservesProjectiveObjects N M i)).subsingleton_congr.symm
    | exact (Equiv.ofBijective _ (Functor.mapExt_bijective_of_preservesProjectiveObjects (ModuleCat.uliftFunctor.{w} R) N M i)).subsingleton_congr.symm
    | exact (Equiv.ofBijective _ (ModuleCat.uliftFunctor_mapExt_bijective N M i)).subsingleton_congr.symm
    | exact (Equiv.ofBijective ((ModuleCat.uliftFunctor.{w} R).mapExt N M i) (by apply Functor.mapExt_bijective_of_preservesProjectiveObjects)).subsingleton_congr.symm
    | exact (Equiv.ofBijective ((ModuleCat.uliftFunctor.{w} R).mapExt N M i) (by apply ModuleCat.uliftFunctor_mapExt_bijective)).subsingleton_congr.symm
  simp only [depth]
  congr
  ext n
  exact forall₂_congr fun i _ ↦ h i
