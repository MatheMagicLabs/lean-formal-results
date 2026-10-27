/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     ZeroDimensionalSpace.of_hasBasis
Source:      Mathlib @ a02a63c2, Mathlib/Topology/InductiveDimension/Classes.lean, line 162
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  A1-astra, arm RS, verified in round 1 (round 0 = first attempt)
Prover:      gpt-6-astra
Setup:       GPT-6 Astra (Codex, effort medium): R = proof plus up to 3 repair rounds with Lean errors; RS = R plus lemma layer; RT = R with read-only Mathlib sources to search; N0-N3 = independent attempts
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
  apply zeroDimensionalSpace_iff_nhds_hasBasis_isClopen.mpr
  intro x
  obtain ⟨ι, p, s, hc, hb⟩ := H x
  refine ⟨fun U ↦ ?_⟩
  constructor
  · intro hU
    obtain ⟨i, hi, hsub⟩ := hb.mem_iff.mp hU
    have hsi : s i ∈ 𝓝 x := hb.mem_iff.mpr ⟨i, hi, Subset.rfl⟩
    exact ⟨s i, ⟨hc i hi, mem_of_mem_nhds hsi⟩, hsub⟩
  · rintro ⟨V, ⟨hV, hxV⟩, hsub⟩
    exact Filter.mem_of_superset (hV.isOpen.mem_nhds hxV) hsub
