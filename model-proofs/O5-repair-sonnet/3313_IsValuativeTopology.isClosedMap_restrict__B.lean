/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     IsValuativeTopology.isClosedMap_restrict
Source:      Mathlib @ a02a63c2, Mathlib/Topology/Algebra/ValuativeRel/Completion.lean, line 157
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  O5-repair-sonnet, arm B, verified in round 1 (round 0 = first attempt)
Prover:      claude-sonnet-5-5
Setup:       Sonnet 5.5: arm B = repair loop; arm A = independent attempts
Check:       the proof replaced the human proof in the Mathlib file above; Lean reported
             0 errors and no `sorry`; sorry/admit/native_decide/search tactics were rejected.
-/

-- (context: the Mathlib file above this declaration)
lemma isClosedMap_restrict :
    IsClosedMap (v.restrict : K → v.ValueGroup₀) := by
  intro s hs
  rw [← isOpen_compl_iff, isOpen_iff_mem_nhds]
  intro γ hγ
  by_cases h0 : γ = 0
  · subst h0
    have h0s : (0 : K) ∈ sᶜ := by
      intro h0s
      exact hγ ⟨0, h0s, map_zero _⟩
    have hnhds : sᶜ ∈ 𝓝 (0 : K) := hs.isOpen_compl.mem_nhds h0s
    obtain ⟨δ, hδ⟩ := (v.mem_nhds_zero_iff _).1 hnhds
    have hmem : Set.Iio (δ : v.ValueGroup₀) ∈ 𝓝 (0 : v.ValueGroup₀) :=
      WithZeroTopology.Iio_mem_nhds (zero_lt_iff.2 δ.ne_zero)
    refine Filter.mem_of_superset hmem ?_
    intro z hz
    rintro ⟨x, hxs, rfl⟩
    have hx : v.restrict x < δ := hz
    have : x ∈ sᶜ := by
      first
        | exact hδ hx
        | exact hδ x hx
    exact this hxs
  · refine Filter.mem_of_superset (WithZeroTopology.singleton_mem_nhds_of_ne_zero h0) ?_
    intro z hz
    rw [Set.mem_singleton_iff] at hz
    subst hz
    exact hγ
