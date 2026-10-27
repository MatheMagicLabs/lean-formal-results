/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     zeroDimensionalSpace_iff_isTopologicalBasis_isClopen
Source:      Mathlib @ a02a63c2, Mathlib/Topology/InductiveDimension/Classes.lean, line 114
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  O3-lemma-layer, arm R, verified in round 2 (round 0 = first attempt)
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
  constructor
  · intro h
    refine isTopologicalBasis_of_isOpen_of_nhds (fun s hs => hs.isOpen) ?_
    intro x U hxU hU
    cases h
    all_goals try simp_all
    all_goals first
      | (rename_i s hs hfr
         obtain ⟨v, hv, hxv, hvU⟩ := hs.exists_subset_of_mem_open hxU hU
         exact ⟨v, isClopen_iff_frontier_eq_empty.mpr (hfr v hv), hxv, hvU⟩)
      | aesop
  · intro h
    first
    | (constructor
       all_goals first
         | (intro x U hU
            obtain ⟨V, hV, hxV, hVU⟩ := h.exists_subset_of_mem_open (mem_of_mem_nhds hU) (isOpen_interior.mono interior_subset |>.elim ‹_› ‹_›)
            exact ⟨V, hV.isOpen, hxV, hVU, by constructor; simp [hV.frontier_eq]⟩)
         | (intro x U hU
            obtain ⟨V, hV, hxV, hVU⟩ := h.mem_nhds_iff.mp hU
            exact ⟨V, hV.isOpen, hxV, hVU, by constructor; simp [hV.frontier_eq]⟩)
         | (intro x U hxU hUo
            obtain ⟨V, hV, hxV, hVU⟩ := h.exists_subset_of_mem_open hxU hUo
            exact ⟨V, hV.isOpen, hxV, hVU, by constructor; simp [hV.frontier_eq]⟩)
         | aesop)
    | aesop
