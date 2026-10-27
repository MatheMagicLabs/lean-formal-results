/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     AffineMap.isAffineMap
Source:      Mathlib @ a02a63c2, Mathlib/Geometry/Convex/ConvexSpace/AffineSpace.lean, line 204
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  O2-repair-vs-resample, arm A, attempt 3, verified in round 0 (round 0 = first attempt)
Prover:      claude-opus-5-5
Setup:       Opus 5.5: arm B = one attempt plus up to 3 repair rounds with Lean error messages; arm A = 4 independent attempts (attempt k)
Check:       the proof replaced the human proof in the Mathlib file above; Lean reported
             0 errors and no `sorry`; sorry/admit/native_decide/search tactics were rejected.
-/

-- (context: the Mathlib file above this declaration)
lemma AffineMap.isAffineMap (f : P₁ →ᵃ[R] P₂) : IsAffineMap R f  where
  map_sConvexComb s := by
     rw [sConvexComb_eq_affineCombination s,
       Finset.map_affineCombination _ _ _ s.total, Function.comp_id]
     first
       | exact (iConvexComb_eq_affineCombination s f).symm
       | exact (iConvexComb_eq_affineCombination s f)
