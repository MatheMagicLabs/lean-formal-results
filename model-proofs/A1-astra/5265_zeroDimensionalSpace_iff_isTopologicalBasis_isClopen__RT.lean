/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     zeroDimensionalSpace_iff_isTopologicalBasis_isClopen
Source:      Mathlib @ a02a63c2, Mathlib/Topology/InductiveDimension/Classes.lean, line 114
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  A1-astra, arm RT, verified in round 0 (round 0 = first attempt)
Prover:      gpt-6-astra
Setup:       GPT-6 Astra (Codex, effort medium): R = proof plus up to 3 repair rounds with Lean errors; RS = R plus lemma layer; RT = R with read-only Mathlib sources to search; N0-N3 = independent attempts
Check:       the proof replaced the human proof in the Mathlib file above; Lean reported
             0 errors and no `sorry`; sorry/admit/native_decide/search tactics were rejected.
-/

open Set Topology TopologicalSpace
variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
variable (X) in
variable (X) in

lemma zeroDimensionalSpace_iff_isTopologicalBasis_isClopen :
    ZeroDimensionalSpace X ↔ IsTopologicalBasis { s : Set X | IsClopen s } := by
  constructor
  · intro h
    cases h
    rename_i s hs h
    refine hs.of_isOpen_of_subset (fun U hU => hU.isOpen) ?_
    intro U hU
    exact isClopen_iff_frontier_eq_empty.mpr
      (Set.isEmpty_coe_sort.mp
        (hasSmallInductiveDimensionLT_zero_iff.mp (h U hU)))
  · intro h
    refine HasSmallInductiveDimensionLT.succ 0 _ h ?_
    intro U hU
    exact hasSmallInductiveDimensionLT_zero_iff.mpr
      (Set.isEmpty_coe_sort.mpr hU.frontier_eq)
