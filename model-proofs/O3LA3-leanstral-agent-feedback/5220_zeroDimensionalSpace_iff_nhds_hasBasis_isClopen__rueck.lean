/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     zeroDimensionalSpace_iff_nhds_hasBasis_isClopen
Source:      Mathlib @ a02a63c2, Mathlib/Topology/InductiveDimension/Classes.lean, line 139
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  O3LA3-leanstral-agent-feedback, arm rueck, verified in final
Prover:      labs-leanstral-1-5
Setup:       Leanstral 1.5 agent with goal-state feedback (arm rueck)
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
    apply zeroDimensionalSpace_iff_isTopologicalBasis_isClopen.2
    apply IsTopologicalBasis.of_hasBasis_nhds
    intro x
    simpa using H x
