/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     ZeroDimensionalSpace.of_isTopologicalBasis
Source:      Mathlib @ a02a63c2, Mathlib/Topology/InductiveDimension/Classes.lean, line 134
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  A1-astra, arm RS, verified in round 0 (round 0 = first attempt)
Prover:      gpt-6-astra
Setup:       GPT-6 Astra (Codex, effort medium): R = proof plus up to 3 repair rounds with Lean errors; RS = R plus lemma layer; RT = R with read-only Mathlib sources to search; N0-N3 = independent attempts
Check:       the proof replaced the human proof in the Mathlib file above; Lean reported
             0 errors and no `sorry`; sorry/admit/native_decide/search tactics were rejected.
-/

open Set Topology TopologicalSpace
variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
variable (X) in
variable (X) in

theorem ZeroDimensionalSpace.of_isTopologicalBasis {u : Set (Set X)} (hs : ∀ s ∈ u, IsClopen s)
    (hu : IsTopologicalBasis u) : ZeroDimensionalSpace X := by
  apply zeroDimensionalSpace_iff_isTopologicalBasis_isClopen.mpr
  exact IsTopologicalBasis.of_isOpen_of_subset
    (fun s hs => hs.isOpen) hu (fun s hs' => hs s hs')
