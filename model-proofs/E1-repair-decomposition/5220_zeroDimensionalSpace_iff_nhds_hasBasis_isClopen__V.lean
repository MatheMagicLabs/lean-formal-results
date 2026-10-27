/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     zeroDimensionalSpace_iff_nhds_hasBasis_isClopen
Source:      Mathlib @ a02a63c2, Mathlib/Topology/InductiveDimension/Classes.lean, line 139
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  E1-repair-decomposition, arm V, verified in round 2 (round 0 = first attempt)
Prover:      gpt-6-astra
Setup:       GPT-6 Astra, which part of Lean feedback makes repair work: after a shared first attempt (E0), V = full error messages, Z = line numbers only, B = only "Lean rejected this proof"
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
    constructor
    · refine isTopologicalBasis_of_isOpen_of_nhds
        (s := {s : Set X | IsClopen s}) ?_ ?_
      · intro s hs
        exact hs.isOpen
      · intro x s hxs hs
        obtain ⟨t, ⟨ht, hxt⟩, hts⟩ := (H x).mem_iff.mp (hs.mem_nhds hxs)
        exact ⟨t, ht, hxt, hts⟩
    · intro U hU
      have hfront : frontier U = ∅ := hU.frontier_eq
      rw [hfront]
      first
      | infer_instance
      | solve | simp
      | constructor <;> simp_all
