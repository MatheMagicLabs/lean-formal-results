/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     zeroDimensionalSpace_iff_isTopologicalBasis_isClopen
Source:      Mathlib @ a02a63c2, Mathlib/Topology/InductiveDimension/Classes.lean, line 114
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  O5-repair-sonnet, arm A, attempt 2, verified in round 0 (round 0 = first attempt)
Prover:      claude-sonnet-5-5
Setup:       Sonnet 5.5: arm B = repair loop; arm A = independent attempts
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
      have hc : ∀ U ∈ s, IsClopen U := fun U hU =>
        isClopen_iff_frontier_eq_empty.2
          (Set.isEmpty_coe_sort.1 (hasSmallInductiveDimensionLT_zero_iff.1 (h U hU)))
      refine isTopologicalBasis_of_isOpen_of_nhds (fun u hu => hu.isOpen) ?_
      intro a u ha hu
      obtain ⟨v, hv, hav, hvu⟩ := hs.exists_subset_of_mem_open ha hu
      exact ⟨v, hc v hv, hav, hvu⟩
  · intro hb
    refine .succ 0 _ hb fun U hU => ?_
    have h1 : frontier U = ∅ := isClopen_iff_frontier_eq_empty.1 hU
    exact hasSmallInductiveDimensionLT_zero_iff.2 (Set.isEmpty_coe_sort.2 h1)
