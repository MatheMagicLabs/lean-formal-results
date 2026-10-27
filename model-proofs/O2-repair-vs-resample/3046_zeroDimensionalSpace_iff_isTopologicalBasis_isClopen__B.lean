/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     zeroDimensionalSpace_iff_isTopologicalBasis_isClopen
Source:      Mathlib @ a02a63c2, Mathlib/Topology/InductiveDimension/Classes.lean, line 114
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  O2-repair-vs-resample, arm B, verified in round 0 (round 0 = first attempt)
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
      refine isTopologicalBasis_of_isOpen_of_nhds (fun u hu => hu.isOpen) fun a u hau hu => ?_
      obtain ⟨v, hv, hav, hvu⟩ := hs.exists_subset_of_mem_open hau hu
      have := h v hv
      rw [hasSmallInductiveDimensionLT_zero_iff, Set.isEmpty_coe_sort] at this
      exact ⟨v, isClopen_iff_frontier_eq_empty.mpr this, hav, hvu⟩
  · intro hB
    exact HasSmallInductiveDimensionLT.succ 0 _ hB fun U hU =>
      hasSmallInductiveDimensionLT_zero_iff.2
        (Set.isEmpty_coe_sort.2 (isClopen_iff_frontier_eq_empty.mp hU))
