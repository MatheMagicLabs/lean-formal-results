/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     zeroDimensionalSpace_iff_nhds_hasBasis_isClopen
Source:      Mathlib @ a02a63c2, Mathlib/Topology/InductiveDimension/Classes.lean, line 139
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  O3-lemma-layer, arm R, verified in round 1 (round 0 = first attempt)
Prover:      claude-opus-5-5
Setup:       Opus 5.5 with repair loop: arm R = repair only; arm RS = repair plus the Lean-checked lemma layer
Check:       the proof replaced the human proof in the Mathlib file above; Lean reported
             0 errors and no `sorry`; sorry/admit/native_decide/search tactics were rejected.
-/

open Set Topology TopologicalSpace
variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
variable (X) in
variable (X) in

theorem zeroDimensionalSpace_iff_nhds_hasBasis_isClopen :
    ZeroDimensionalSpace X ↔ ∀ x : X, (𝓝 x).HasBasis (fun s ↦ IsClopen s ∧ x ∈ s) id where
  mp _ _ := isTopologicalBasis_isClopen.nhds_hasBasis
  mpr H := by
    have hB : IsTopologicalBasis {s : Set X | IsClopen s} := by
      refine isTopologicalBasis_of_isOpen_of_nhds (fun u hu => IsClopen.isOpen hu) ?_
      intro a u ha hu
      obtain ⟨v, ⟨hv, hav⟩, hvu⟩ := (H a).mem_iff.mp (hu.mem_nhds ha)
      exact ⟨v, hv, hav, hvu⟩
    first
    | exact (zeroDimensionalSpace_iff_isTopologicalBasis_isClopen X).mpr hB
    | exact zeroDimensionalSpace_iff_isTopologicalBasis_isClopen.mpr hB
    | exact (zeroDimensionalSpace_iff_isTopologicalBasis X).mpr hB
    | exact zeroDimensionalSpace_iff_isTopologicalBasis.mpr hB
    | exact ZeroDimensionalSpace.of_isTopologicalBasis hB
    | exact ZeroDimensionalSpace.of_isTopologicalBasis_isClopen hB
    | exact hB.zeroDimensionalSpace
    | exact ZeroDimensionalSpace.mk hB
    | exact (zeroDimensionalSpace_iff X).mpr hB
    | exact zeroDimensionalSpace_iff.mpr hB
