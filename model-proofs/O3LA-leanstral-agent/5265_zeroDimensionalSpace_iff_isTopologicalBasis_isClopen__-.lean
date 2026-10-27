/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     zeroDimensionalSpace_iff_isTopologicalBasis_isClopen
Source:      Mathlib @ a02a63c2, Mathlib/Topology/InductiveDimension/Classes.lean, line 114
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  O3LA-leanstral-agent, arm -, verified in final
Prover:      labs-leanstral-1-5
Setup:       Leanstral 1.5 as a tool-using agent (Mistral Vibe)
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
    | succ n s hs h =>
      have hclopen : ∀ U ∈ s, IsClopen U := by
        intro U hU
        have h_empty : IsEmpty (frontier U) :=
          (hasSmallInductiveDimensionLT_zero_iff.mp (h U hU))
        have h_frontier_empty : frontier U = ∅ := by
          ext x; constructor
          · intro hx; exact h_empty.elim ⟨x, hx⟩
          · intro hx; exact hx.elim
        exact isClopen_iff_frontier_eq_empty.mpr h_frontier_empty
      have h_open : ∀ (u : Set X), u ∈ {s | IsClopen s} → IsOpen u := by
        intro u hu
        exact (hu.2 : IsOpen u)
      have h_sub : s ⊆ {s | IsClopen s} := hclopen
      exact hs.of_isOpen_of_subset h_open h_sub
  · intro h
    refine .succ 0 {s | IsClopen s} h ?_
    intro U hU
    have h_frontier_empty : frontier U = ∅ := hU.frontier_eq
    rw [h_frontier_empty]
    exact .zero
