/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     zeroDimensionalSpace_iff_isTopologicalBasis_isClopen
Source:      Mathlib @ a02a63c2, Mathlib/Topology/InductiveDimension/Classes.lean, line 114
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  A1-astra, arm R, verified in round 2 (round 0 = first attempt)
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
    cases h with
    | succ n B hB hfrontier =>
      refine IsTopologicalBasis.of_isOpen_of_subset
        (fun U hU => hU.isOpen) hB ?_
      intro U hU
      apply isClopen_iff_frontier_eq_empty.mpr
      haveI : IsEmpty (frontier U) :=
        hasSmallInductiveDimensionLT_zero_iff.mp (hfrontier U hU)
      apply Set.eq_empty_iff_forall_notMem.mpr
      intro x hx
      exact isEmptyElim (⟨x, hx⟩ : frontier U)
  · intro h
    refine HasSmallInductiveDimensionLT.succ 0
      {U : Set X | IsClopen U} h ?_
    intro U hU
    apply hasSmallInductiveDimensionLT_zero_iff.mpr
    refine ⟨fun x => ?_⟩
    rcases x with ⟨x, hx⟩
    rw [hU.frontier_eq] at hx
    exact hx
