/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     ZeroDimensionalSpace.of_hasBasis
Source:      Mathlib @ a02a63c2, Mathlib/Topology/InductiveDimension/Classes.lean, line 162
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  O2-repair-vs-resample, arm A, attempt 3, verified in round 0 (round 0 = first attempt)
Prover:      claude-opus-5-5
Setup:       Opus 5.5: arm B = one attempt plus up to 3 repair rounds with Lean error messages; arm A = 4 independent attempts (attempt k)
Check:       the proof replaced the human proof in the Mathlib file above; Lean reported
             0 errors and no `sorry`; sorry/admit/native_decide/search tactics were rejected.
-/

-- (context: the Mathlib file above this declaration)
theorem ZeroDimensionalSpace.of_hasBasis
    (H : ∀ x : X, ∃ (ι : Sort*) (p : ι → Prop) (s : ι → Set X),
      (∀ i, p i → IsClopen (s i)) ∧ (𝓝 x).HasBasis p s) :
    ZeroDimensionalSpace X := by
  rw [zeroDimensionalSpace_iff_nhds_hasBasis_isClopen]
  intro x
  obtain ⟨ι, p, s, hs, hb⟩ := H x
  refine ⟨fun t => ⟨fun ht => ?_, ?_⟩⟩
  · obtain ⟨i, hi, hsub⟩ := hb.mem_iff.1 ht
    exact ⟨s i, ⟨hs i hi, mem_of_mem_nhds (hb.mem_of_mem hi)⟩, hsub⟩
  · rintro ⟨u, ⟨hu, hxu⟩, hut⟩
    exact Filter.mem_of_superset (hu.isOpen.mem_nhds hxu) hut
