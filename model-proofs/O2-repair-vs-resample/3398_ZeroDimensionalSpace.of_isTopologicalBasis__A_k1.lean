/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     ZeroDimensionalSpace.of_isTopologicalBasis
Source:      Mathlib @ a02a63c2, Mathlib/Topology/InductiveDimension/Classes.lean, line 134
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  O2-repair-vs-resample, arm A, attempt 1, verified in round 0 (round 0 = first attempt)
Prover:      claude-opus-5-5
Setup:       Opus 5.5: arm B = one attempt plus up to 3 repair rounds with Lean error messages; arm A = 4 independent attempts (attempt k)
Check:       the proof replaced the human proof in the Mathlib file above; Lean reported
             0 errors and no `sorry`; sorry/admit/native_decide/search tactics were rejected.
-/

-- (context: the Mathlib file above this declaration)
theorem ZeroDimensionalSpace.of_isTopologicalBasis {u : Set (Set X)} (hs : ∀ s ∈ u, IsClopen s)
    (hu : IsTopologicalBasis u) : ZeroDimensionalSpace X := by
  rw [zeroDimensionalSpace_iff_isTopologicalBasis_isClopen]
  exact hu.of_isOpen_of_subset (fun _ h => h.isOpen) (fun s h => hs s h)
