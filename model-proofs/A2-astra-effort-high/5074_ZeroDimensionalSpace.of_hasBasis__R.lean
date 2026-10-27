/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     ZeroDimensionalSpace.of_hasBasis
Source:      Mathlib @ a02a63c2, Mathlib/Topology/InductiveDimension/Classes.lean, line 162
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  A2-astra-effort-high, arm R, verified in round 1 (round 0 = first attempt)
Prover:      gpt-6-astra
Setup:       GPT-6 Astra, reasoning effort high (arms R, N0)
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
  · change IsTopologicalBasis {U : Set X | IsClopen U}
    apply isTopologicalBasis_of_isOpen_of_nhds
    · intro U hU
      exact hU.isOpen
    · intro x U hx hU
      obtain ⟨ι, p, s, hcl, hb⟩ := H x
      obtain ⟨i, hi, hiU⟩ := hb.mem_iff.mp (hU.mem_nhds hx)
      refine ⟨s i, hcl i hi, ?_, hiU⟩
      exact mem_of_mem_nhds (hb.mem_iff.mpr ⟨i, hi, Subset.rfl⟩)
  · intro U hU
    have hcl : IsClopen U := hU
    have hf : frontier U = ∅ := by
      rw [frontier, hcl.isClosed.closure_eq, hcl.isOpen.interior_eq,
        diff_self]
    rw [hf]
    constructor <;> infer_instance
