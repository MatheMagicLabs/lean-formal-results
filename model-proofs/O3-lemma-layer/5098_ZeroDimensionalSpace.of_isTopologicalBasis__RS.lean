/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     ZeroDimensionalSpace.of_isTopologicalBasis
Source:      Mathlib @ a02a63c2, Mathlib/Topology/InductiveDimension/Classes.lean, line 134
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  O3-lemma-layer, arm RS, verified in round 0 (round 0 = first attempt)
Prover:      claude-opus-5-5
Setup:       Opus 5.5 with repair loop: arm R = repair only; arm RS = repair plus the Lean-checked lemma layer
Check:       the proof replaced the human proof in the Mathlib file above; Lean reported
             0 errors and no `sorry`; sorry/admit/native_decide/search tactics were rejected.
-/

open Set Topology TopologicalSpace
variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
variable (X) in
variable (X) in

theorem ZeroDimensionalSpace.of_isTopologicalBasis {u : Set (Set X)} (hs : ∀ s ∈ u, IsClopen s)
    (hu : IsTopologicalBasis u) : ZeroDimensionalSpace X := by
  rw [zeroDimensionalSpace_iff_isTopologicalBasis_isClopen]
  exact hu.of_isOpen_of_subset (fun v hv => (show IsClopen v from hv).isOpen) hs
