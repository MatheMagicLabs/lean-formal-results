/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     ZeroDimensionalSpace.of_hasBasis
Source:      Mathlib @ a02a63c2, Mathlib/Topology/InductiveDimension/Classes.lean, line 162
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

theorem ZeroDimensionalSpace.of_hasBasis
    (H : ∀ x : X, ∃ (ι : Sort*) (p : ι → Prop) (s : ι → Set X),
      (∀ i, p i → IsClopen (s i)) ∧ (𝓝 x).HasBasis p s) :
    ZeroDimensionalSpace X := by
  rw [zeroDimensionalSpace_iff_nhds_hasBasis_isClopen]
  intro x
  obtain ⟨ι, p, s, hc, hb⟩ := H x
  refine hb.to_hasBasis
    (fun i hi => ⟨s i, ⟨hc i hi, mem_of_mem_nhds (hb.mem_of_mem hi)⟩, subset_rfl⟩)
    (fun t ht => ?_)
  obtain ⟨i, hi, hsub⟩ := hb.mem_iff.1 (ht.1.isOpen.mem_nhds ht.2)
  exact ⟨i, hi, hsub⟩
