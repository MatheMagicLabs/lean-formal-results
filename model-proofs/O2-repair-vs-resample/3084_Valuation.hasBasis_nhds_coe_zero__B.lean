/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     Valuation.hasBasis_nhds_coe_zero
Source:      Mathlib @ a02a63c2, Mathlib/Topology/Algebra/ValuativeRel/Completion.lean, line 430
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  O2-repair-vs-resample, arm B, verified in round 1 (round 0 = first attempt)
Prover:      claude-opus-5-5
Setup:       Opus 5.5: arm B = one attempt plus up to 3 repair rounds with Lean error messages; arm A = 4 independent attempts (attempt k)
Check:       the proof replaced the human proof in the Mathlib file above; Lean reported
             0 errors and no `sorry`; sorry/admit/native_decide/search tactics were rejected.
-/

-- (context: the Mathlib file above this declaration)
theorem hasBasis_nhds_coe_zero :
    (𝓝 (0 : Completion K)).HasBasis (fun _ ↦ True)
      fun γ : v.extension.ValueGroup₀ˣ ↦ {x | v.extension.restrict x < γ.1} := by
  refine ⟨fun t ↦ ⟨fun ht ↦ ?_, ?_⟩⟩
  · obtain ⟨s, ⟨hs, hsc⟩, hst⟩ := (closed_nhds_basis (0 : Completion K)).mem_iff.1 ht
    have hs' : ((↑) : K → Completion K) ⁻¹' s ∈ 𝓝 (0 : K) := by
      have htend := (Completion.continuous_coe K).tendsto (0 : K)
      rw [Completion.coe_zero] at htend
      exact htend hs
    obtain ⟨γ, hγ⟩ := (v.mem_nhds_zero_iff _).1 hs'
    refine ⟨Units.map v.valueGroup₀ExtensionEquiv.toMonoidHom γ, trivial, fun x hx ↦ hst ?_⟩
    have hcl : closure (((↑) : K → Completion K) '' {x : K | v.restrict x < γ.1}) ⊆ s :=
      hsc.closure_subset_iff.2 (Set.image_subset_iff.2 hγ)
    apply hcl
    rw [v.closure_image_coe_ofPred_restrict_lt]
    have := (v.extension.restrict_lt_iff_lt_embedding).1 hx
    simpa using this
  · rintro ⟨γ, -, hγ⟩
    refine Filter.mem_of_superset ?_ hγ
    have h1 : {x : K | v.restrict x <
        (Units.map v.valueGroup₀ExtensionEquiv.symm.toMonoidHom γ).1} ∈ 𝓝 (0 : K) :=
      (v.mem_nhds_zero_iff _).2 ⟨Units.map v.valueGroup₀ExtensionEquiv.symm.toMonoidHom γ,
        subset_rfl⟩
    have h2 := Completion.isDenseInducing_coe.closure_image_mem_nhds h1
    rw [v.closure_image_coe_ofPred_restrict_lt, Completion.coe_zero] at h2
    refine Filter.mem_of_superset h2 fun x hx ↦ ?_
    apply v.extension.restrict_lt_iff_lt_embedding.2
    simpa using hx
