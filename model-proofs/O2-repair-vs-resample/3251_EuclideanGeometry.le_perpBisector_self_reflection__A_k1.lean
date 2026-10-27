/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     EuclideanGeometry.le_perpBisector_self_reflection
Source:      Mathlib @ a02a63c2, Mathlib/Geometry/Euclidean/Projection.lean, line 585
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  O2-repair-vs-resample, arm A, attempt 1, verified in round 0 (round 0 = first attempt)
Prover:      claude-opus-5-5
Setup:       Opus 5.5: arm B = one attempt plus up to 3 repair rounds with Lean error messages; arm A = 4 independent attempts (attempt k)
Check:       the proof replaced the human proof in the Mathlib file above; Lean reported
             0 errors and no `sorry`; sorry/admit/native_decide/search tactics were rejected.
-/

-- (context: the Mathlib file above this declaration)
theorem le_perpBisector_self_reflection (s : AffineSubspace ℝ P) [Nonempty s]
    [s.direction.HasOrthogonalProjection] (a : P) :
    s ≤ perpBisector a (reflection s a) := by
  intro p hp
  rw [mem_perpBisector_iff_dist_eq]
  exact (dist_reflection_eq_of_mem s hp a).symm
