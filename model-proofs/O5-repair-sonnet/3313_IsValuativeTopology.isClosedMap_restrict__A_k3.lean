/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     IsValuativeTopology.isClosedMap_restrict
Source:      Mathlib @ a02a63c2, Mathlib/Topology/Algebra/ValuativeRel/Completion.lean, line 157
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  O5-repair-sonnet, arm A, attempt 3, verified in round 0 (round 0 = first attempt)
Prover:      claude-sonnet-5-5
Setup:       Sonnet 5.5: arm B = repair loop; arm A = independent attempts
Check:       the proof replaced the human proof in the Mathlib file above; Lean reported
             0 errors and no `sorry`; sorry/admit/native_decide/search tactics were rejected.
-/

-- (context: the Mathlib file above this declaration)
lemma isClosedMap_restrict :
    IsClosedMap (v.restrict : K → v.ValueGroup₀) := by
  intro F hF
  rw [← isOpen_compl_iff, WithZeroTopology.isOpen_iff]
  by_cases h0 : (0 : v.ValueGroup₀) ∈ v.restrict '' F
  · left
    exact fun h => h h0
  · right
    have h : (0 : K) ∈ Fᶜ := fun h0F => h0 ⟨0, h0F, by simp⟩
    obtain ⟨γ, hγ⟩ := (v.mem_nhds_zero_iff Fᶜ).1 (hF.isOpen_compl.mem_nhds h)
    have hsub : Set.Iio (γ : v.ValueGroup₀) ⊆ (v.restrict '' F)ᶜ := by
      intro z hz
      rintro ⟨x, hxF, rfl⟩
      exact hγ hz hxF
    first
      | exact ⟨γ, γ.ne_zero, hsub⟩
      | exact ⟨γ, hsub⟩
