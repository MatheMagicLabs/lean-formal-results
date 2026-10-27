/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     zeroDimensionalSpace_iff_isTopologicalBasis_isClopen
Source:      Mathlib @ a02a63c2, Mathlib/Topology/InductiveDimension/Classes.lean, line 114
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  O3-lemma-layer, arm RS, verified in round 3 (round 0 = first attempt)
Prover:      claude-opus-5-5
Setup:       Opus 5.5 with repair loop: arm R = repair only; arm RS = repair plus the Lean-checked lemma layer
Check:       the proof replaced the human proof in the Mathlib file above; Lean reported
             0 errors and no `sorry`; sorry/admit/native_decide/search tactics were rejected.
-/

open Set Topology TopologicalSpace
variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
variable (X) in
variable (X) in

lemma zeroDimensionalSpace_iff_isTopologicalBasis_isClopen :
    ZeroDimensionalSpace X ↔ IsTopologicalBasis { s : Set X | IsClopen s } := by
  rw [zeroDimensionalSpace_def]
  constructor
  · intro h
    cases h
    all_goals
      refine isTopologicalBasis_of_isOpen_of_nhds (fun u hu => hu.isOpen) ?_
      intro x u hxu hu
      obtain ⟨v, hvB, hxv, hvu⟩ :=
        (‹IsTopologicalBasis _›).exists_subset_of_mem_open hxu hu
      refine ⟨v, ?_, hxv, hvu⟩
      have hvo : IsOpen v := (‹IsTopologicalBasis _›).isOpen hvB
      have hf := ‹∀ U ∈ _, _› v hvB
      show IsClopen v
      rw [isClopen_iff_frontier_eq_empty]
      cases hf
      all_goals first
        | exact Set.isEmpty_coe_sort.mp ‹_›
        | (rename_i he; exact Set.isEmpty_coe_sort.mp he)
        | simp_all [Set.isEmpty_coe_sort]
  · intro h
    constructor
    all_goals first | exact h | skip
    all_goals
      intro U hU
      have he : IsEmpty (frontier U) :=
        Set.isEmpty_coe_sort.mpr (isClopen_iff_frontier_eq_empty.mp hU)
      first
        | constructor
        | (constructor <;> assumption)
        | simp_all
