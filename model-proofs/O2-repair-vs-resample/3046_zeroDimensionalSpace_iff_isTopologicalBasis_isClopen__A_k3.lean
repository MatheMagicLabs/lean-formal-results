/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     zeroDimensionalSpace_iff_isTopologicalBasis_isClopen
Source:      Mathlib @ a02a63c2, Mathlib/Topology/InductiveDimension/Classes.lean, line 114
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  O2-repair-vs-resample, arm A, attempt 3, verified in round 0 (round 0 = first attempt)
Prover:      claude-opus-5-5
Setup:       Opus 5.5: arm B = one attempt plus up to 3 repair rounds with Lean error messages; arm A = 4 independent attempts (attempt k)
Check:       the proof replaced the human proof in the Mathlib file above; Lean reported
             0 errors and no `sorry`; sorry/admit/native_decide/search tactics were rejected.
-/

-- (context: the Mathlib file above this declaration)
lemma zeroDimensionalSpace_iff_isTopologicalBasis_isClopen :
    ZeroDimensionalSpace X ↔ IsTopologicalBasis { s : Set X | IsClopen s } := by
  constructor
  · intro H
    cases H with
    | succ n s hs h =>
      refine hs.of_isOpen_of_subset (fun u hu => hu.isOpen) fun U hU => ?_
      have h1 := hasSmallInductiveDimensionLT_zero_iff.1 (h U hU)
      have h2 : frontier U = ∅ := Set.isEmpty_coe_sort.1 h1
      refine ⟨frontier_subset_iff_isClosed.1 ?_, hs.isOpen hU⟩
      rw [h2]
      exact empty_subset _
  · intro h
    exact .succ 0 _ h fun U hU =>
      hasSmallInductiveDimensionLT_zero_iff.2 (Set.isEmpty_coe_sort.2 hU.frontier_eq)
