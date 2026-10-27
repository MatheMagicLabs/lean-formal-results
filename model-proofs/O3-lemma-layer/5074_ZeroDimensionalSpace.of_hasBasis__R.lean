/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     ZeroDimensionalSpace.of_hasBasis
Source:      Mathlib @ a02a63c2, Mathlib/Topology/InductiveDimension/Classes.lean, line 162
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

theorem ZeroDimensionalSpace.of_hasBasis
    (H : ∀ x : X, ∃ (ι : Sort*) (p : ι → Prop) (s : ι → Set X),
      (∀ i, p i → IsClopen (s i)) ∧ (𝓝 x).HasBasis p s) :
    ZeroDimensionalSpace X := by
  have key : IsTopologicalBasis {s : Set X | IsClopen s} := by
    refine isTopologicalBasis_of_isOpen_of_nhds (fun u hu => hu.isOpen) ?_
    intro a u ha hu
    obtain ⟨ι, p, s, hc, hb⟩ := H a
    obtain ⟨i, hi, hsu⟩ := hb.mem_iff.mp (hu.mem_nhds ha)
    exact ⟨s i, hc i hi, mem_of_mem_nhds (hb.mem_of_mem hi), hsu⟩
  constructor
  · exact key
  · intro U hU
    have hU' : IsClopen U := hU
    have he : IsEmpty (frontier U) := by
      rw [hU'.frontier_eq]
      infer_instance
    first
      | exact HasSmallInductiveDimensionLT.of_isEmpty
      | exact hasSmallInductiveDimensionLT_zero_iff.mpr he
      | exact hasSmallInductiveDimensionLT_zero_iff_isEmpty.mpr he
      | exact HasSmallInductiveDimensionLT.of_isEmpty _
      | exact (hasSmallInductiveDimensionLT_zero_iff _).mpr he
      | (rw [hasSmallInductiveDimensionLT_zero_iff]; exact he)
      | (constructor; exact he)
      | (constructor <;> simp_all)
      | simp_all [HasSmallInductiveDimensionLT]
