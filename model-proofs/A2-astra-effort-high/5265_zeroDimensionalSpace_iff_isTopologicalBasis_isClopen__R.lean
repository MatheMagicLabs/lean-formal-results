/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     zeroDimensionalSpace_iff_isTopologicalBasis_isClopen
Source:      Mathlib @ a02a63c2, Mathlib/Topology/InductiveDimension/Classes.lean, line 114
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  A2-astra-effort-high, arm R, verified in round 3 (round 0 = first attempt)
Prover:      gpt-6-astra
Setup:       GPT-6 Astra, reasoning effort high (arms R, N0)
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
    rename_i B hB hdim
    refine isTopologicalBasis_of_isOpen_of_nhds (fun s hs => hs.isOpen) ?_
    intro x U hxU hU
    obtain ⟨s, hs, hxs, hsU⟩ := hB.mem_nhds_iff.mp (hU.mem_nhds hxU)
    have hc : IsClopen s := by
      simpa only [Set.isEmpty_coe_sort, ← isClopen_iff_frontier_eq_empty]
        using hasSmallInductiveDimensionLT_zero_iff.mp (hdim s hs)
    exact ⟨s, hc, hxs, hsU⟩
  · intro h
    constructor
    · exact h
    · intro s hs
      change IsClopen s at hs
      apply hasSmallInductiveDimensionLT_zero_iff.mpr
      simpa only [Set.isEmpty_coe_sort, ← isClopen_iff_frontier_eq_empty]
        using hs
