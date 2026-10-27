/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     Valuation.hasBasis_nhds_coe_zero
Source:      Mathlib @ a02a63c2, Mathlib/Topology/Algebra/ValuativeRel/Completion.lean, line 430
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  O5-repair-sonnet, arm A, attempt 0, verified in round 0 (round 0 = first attempt)
Prover:      claude-sonnet-5-5
Setup:       Sonnet 5.5: arm B = repair loop; arm A = independent attempts
Check:       the proof replaced the human proof in the Mathlib file above; Lean reported
             0 errors and no `sorry`; sorry/admit/native_decide/search tactics were rejected.
-/

-- (context: the Mathlib file above this declaration)
theorem hasBasis_nhds_coe_zero :
    (𝓝 (0 : Completion K)).HasBasis (fun _ ↦ True)
      fun γ : v.extension.ValueGroup₀ˣ ↦ {x | v.extension.restrict x < γ.1} := by
  have key : ∀ γ : v.ValueGroup₀ˣ,
      {x : Completion K | v.extension.restrict x < v.valueGroup₀ExtensionEquiv γ.1} =
        closure ((↑) '' {x : K | v.restrict x < γ.1}) := by
    intro γ
    rw [v.closure_image_coe_ofPred_restrict_lt]
    ext x
    simp [restrict_lt_iff_lt_embedding]
  refine hasBasis_iff.2 fun U => ?_
  constructor
  · intro hU
    obtain ⟨V, ⟨hV, hVc⟩, hVU⟩ := (closed_nhds_basis (0 : Completion K)).mem_iff.1 hU
    have hpre : ((↑) : K → Completion K) ⁻¹' V ∈ 𝓝 (0 : K) :=
      (Completion.continuous_coe K).continuousAt.preimage_mem_nhds (by rwa [Completion.coe_zero])
    obtain ⟨γ, hγ⟩ := (v.mem_nhds_zero_iff _).1 hpre
    refine ⟨Units.map v.valueGroup₀ExtensionEquiv.toMonoidHom γ, trivial, ?_⟩
    change {x : Completion K | v.extension.restrict x < v.valueGroup₀ExtensionEquiv γ.1} ⊆ U
    rw [key γ]
    exact (closure_minimal (image_subset_iff.2 hγ) hVc).trans hVU
  · rintro ⟨γ, -, hγ⟩
    refine Filter.mem_of_superset ?_ hγ
    let γ0 : v.ValueGroup₀ˣ := Units.map v.valueGroup₀ExtensionEquiv.symm.toMonoidHom γ
    have hγ0 : v.valueGroup₀ExtensionEquiv γ0.1 = γ.1 :=
      MulEquiv.apply_symm_apply _ _
    have h1 := key γ0
    rw [hγ0] at h1
    rw [h1]
    have h2 := Completion.isDenseInducing_coe.closure_image_mem_nhds
      ((v.mem_nhds_zero_iff _).2 ⟨γ0, subset_rfl⟩ :
        {x : K | v.restrict x < γ0.1} ∈ 𝓝 (0 : K))
    rwa [Completion.coe_zero] at h2
