/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     Valuation.hasBasis_nhds_coe_zero
Source:      Mathlib @ a02a63c2, Mathlib/Topology/Algebra/ValuativeRel/Completion.lean, line 430
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  O5-repair-sonnet, arm A, attempt 1, verified in round 0 (round 0 = first attempt)
Prover:      claude-sonnet-5-5
Setup:       Sonnet 5.5: arm B = repair loop; arm A = independent attempts
Check:       the proof replaced the human proof in the Mathlib file above; Lean reported
             0 errors and no `sorry`; sorry/admit/native_decide/search tactics were rejected.
-/

-- (context: the Mathlib file above this declaration)
theorem hasBasis_nhds_coe_zero :
    (𝓝 (0 : Completion K)).HasBasis (fun _ ↦ True)
      fun γ : v.extension.ValueGroup₀ˣ ↦ {x | v.extension.restrict x < γ.1} := by
  have di : IsDenseInducing ((↑) : K → Completion K) := Completion.isDenseInducing_coe
  have key : ∀ γ : v.ValueGroup₀ˣ, {x : Completion K | v.extension.restrict x <
      (Units.map v.valueGroup₀ExtensionEquiv.toMonoidHom γ).1} =
      closure ((↑) '' {x : K | v.restrict x < γ.1}) := by
    intro γ
    rw [closure_image_coe_ofPred_restrict_lt]
    ext x
    simp [restrict_lt_iff_lt_embedding]
  refine ⟨fun t => ?_⟩
  simp only [true_and]
  constructor
  · intro ht
    obtain ⟨s, hs, hsc, hst⟩ := exists_mem_nhds_isClosed_subset ht
    have h1 : ((↑) : K → Completion K) ⁻¹' s ∈ 𝓝 (0 : K) := by
      apply di.continuous.continuousAt.preimage_mem_nhds
      rwa [Completion.coe_zero]
    obtain ⟨γ, hγ⟩ := (v.mem_nhds_zero_iff _).1 h1
    refine ⟨Units.map v.valueGroup₀ExtensionEquiv.toMonoidHom γ, ?_⟩
    rw [key]
    refine (closure_minimal ?_ hsc).trans hst
    rintro _ ⟨x, hx, rfl⟩
    exact hγ hx
  · rintro ⟨γ, hγ⟩
    obtain ⟨γ0, rfl⟩ : ∃ γ0 : v.ValueGroup₀ˣ,
        Units.map v.valueGroup₀ExtensionEquiv.toMonoidHom γ0 = γ :=
      ⟨Units.map v.valueGroup₀ExtensionEquiv.symm.toMonoidHom γ, by ext; simp⟩
    rw [key] at hγ
    refine Filter.mem_of_superset ?_ hγ
    have := di.closure_image_mem_nhds
      ((v.mem_nhds_zero_iff _).2 ⟨γ0, fun _ hx => hx⟩ :
        {x : K | v.restrict x < γ0.1} ∈ 𝓝 (0 : K))
    rwa [Completion.coe_zero] at this
