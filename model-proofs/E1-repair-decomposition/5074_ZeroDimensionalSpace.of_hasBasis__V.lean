/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     ZeroDimensionalSpace.of_hasBasis
Source:      Mathlib @ a02a63c2, Mathlib/Topology/InductiveDimension/Classes.lean, line 162
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

theorem ZeroDimensionalSpace.of_hasBasis
    (H : ∀ x : X, ∃ (ι : Sort*) (p : ι → Prop) (s : ι → Set X),
      (∀ i, p i → IsClopen (s i)) ∧ (𝓝 x).HasBasis p s) :
    ZeroDimensionalSpace X := by
  constructor
  · change IsTopologicalBasis {s : Set X | IsClopen s}
    refine isTopologicalBasis_of_isOpen_of_nhds
      (fun s hs => hs.isOpen) ?_
    intro x U hxU hU
    obtain ⟨ι, p, s, hs, hb⟩ := H x
    obtain ⟨i, hi, hiU⟩ := hb.mem_iff.mp (hU.mem_nhds hxU)
    have hsi : s i ∈ 𝓝 x := hb.mem_iff.mpr ⟨i, hi, Subset.rfl⟩
    exact ⟨s i, hs i hi, mem_of_mem_nhds hsi, hiU⟩
  · intro U hU
    have hclopen : IsClopen U := hU
    have hfrontier : frontier U = ∅ := by
      simp [frontier, hclopen.isClosed.closure_eq, hclopen.isOpen.interior_eq]
    rw [hfrontier]
    infer_instance
