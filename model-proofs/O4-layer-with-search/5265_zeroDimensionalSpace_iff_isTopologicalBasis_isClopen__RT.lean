/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     zeroDimensionalSpace_iff_isTopologicalBasis_isClopen
Source:      Mathlib @ a02a63c2, Mathlib/Topology/InductiveDimension/Classes.lean, line 114
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  O4-layer-with-search, arm RT, verified in round 1 (round 0 = first attempt)
Prover:      claude-opus-5-5
Setup:       Opus 5.5 with repair loop, lemma layer and name search (arm RT)
Check:       the proof replaced the human proof in the Mathlib file above; Lean reported
             0 errors and no `sorry`; sorry/admit/native_decide/search tactics were rejected.
-/

open Set Topology TopologicalSpace
variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
variable (X) in
variable (X) in

lemma zeroDimensionalSpace_iff_isTopologicalBasis_isClopen :
    ZeroDimensionalSpace X ↔ IsTopologicalBasis { s : Set X | IsClopen s } := by
  have key : ∀ U : Set X, (IsOpen U ∧ HasSmallInductiveDimensionLT (frontier U) 0) ↔ IsClopen U := by
    intro U
    rw [hasSmallInductiveDimensionLT_zero_iff, isEmpty_coe_sort, ← isClopen_iff_frontier_eq_empty]
    exact ⟨fun h => h.2, fun h => ⟨h.isOpen, h⟩⟩
  rw [zeroDimensionalSpace_def]
  constructor
  · intro h
    cases h
    rename_i hb hfr
    first
    | exact hb.of_isOpen_of_subset (fun U hU => hU.isOpen)
        (fun U hU => (key U).1 ⟨hb.isOpen hU, hfr U hU⟩)
    | exact hfr.of_isOpen_of_subset (fun U hU => hU.isOpen)
        (fun U hU => (key U).1 ⟨hfr.isOpen hU, hb U hU⟩)
  · intro h
    constructor
    all_goals first
      | exact h
      | (intro U hU; exact ((key U).2 hU).2)
      | skip
