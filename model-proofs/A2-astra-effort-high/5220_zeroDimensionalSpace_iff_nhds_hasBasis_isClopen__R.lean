/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     zeroDimensionalSpace_iff_nhds_hasBasis_isClopen
Source:      Mathlib @ a02a63c2, Mathlib/Topology/InductiveDimension/Classes.lean, line 139
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  A2-astra-effort-high, arm R, verified in round 2 (round 0 = first attempt)
Prover:      gpt-6-astra
Setup:       GPT-6 Astra, reasoning effort high (arms R, N0)
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
    rw [zeroDimensionalSpace_iff_isTopologicalBasis_isClopen]
    refine isTopologicalBasis_of_isOpen_of_nhds (fun s hs ↦ hs.isOpen) ?_
    intro x s hxs hs
    rcases (H x).mem_iff.mp (hs.mem_nhds hxs) with ⟨t, ⟨ht, hxt⟩, hts⟩
    exact ⟨t, ht, hxt, hts⟩
