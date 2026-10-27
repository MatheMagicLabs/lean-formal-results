/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     Valuation.hasBasis_nhds_coe_zero
Source:      Mathlib @ a02a63c2, Mathlib/Topology/Algebra/ValuativeRel/Completion.lean, line 430
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  O5-repair-sonnet, arm B, verified in round 0 (round 0 = first attempt)
Prover:      claude-sonnet-5-5
Setup:       Sonnet 5.5: arm B = repair loop; arm A = independent attempts
Check:       the proof replaced the human proof in the Mathlib file above; Lean reported
             0 errors and no `sorry`; sorry/admit/native_decide/search tactics were rejected.
-/

-- (context: the Mathlib file above this declaration)
theorem hasBasis_nhds_coe_zero :
    (𝓝 (0 : Completion K)).HasBasis (fun _ ↦ True)
      fun γ : v.extension.ValueGroup₀ˣ ↦ {x | v.extension.restrict x < γ.1} := by
  refine ⟨fun t => ?_⟩
  constructor
  · intro ht
    obtain ⟨s, ⟨hs, hsc⟩, hst⟩ := (closed_nhds_basis (0 : Completion K)).mem_iff.1 ht
    have h1 : ((↑) ⁻¹' s : Set K) ∈ 𝓝 (0 : K) := by
      apply (Completion.continuous_coe K).continuousAt.preimage_mem_nhds
      rwa [Completion.coe_zero]
    obtain ⟨γ', hγ'⟩ := (v.mem_nhds_zero_iff _).1 h1
    refine ⟨Units.map v.valueGroup₀ExtensionEquiv.toMonoidHom γ', trivial, ?_⟩
    intro x hx
    apply hst
    have hx' := (v.extension.restrict_lt_iff_lt_embedding).1 hx
    have e : embedding ((Units.map v.valueGroup₀ExtensionEquiv.toMonoidHom γ').1)
        = embedding γ'.1 := embedding_valueGroup₀ExtensionEquiv v γ'.1
    have hx'' : v.extension x < embedding γ'.1 := lt_of_lt_of_eq hx' e
    have hmem : x ∈ closure ((↑) '' {x : K | v.restrict x < γ'.1}) := by
      rw [closure_image_coe_ofPred_restrict_lt]
      exact hx''
    exact closure_minimal (image_subset_iff.2 hγ') hsc hmem
  · rintro ⟨γ, -, h⟩
    refine Filter.mem_of_superset ?_ h
    let γ' : v.ValueGroup₀ˣ := Units.map v.valueGroup₀ExtensionEquiv.symm.toMonoidHom γ
    have hK : {x : K | v.restrict x < γ'.1} ∈ 𝓝 (0 : K) :=
      (v.mem_nhds_zero_iff _).2 ⟨γ', subset_rfl⟩
    have := (Completion.isDenseInducing_coe (α := K)).closure_image_mem_nhds hK
    rw [Completion.coe_zero] at this
    refine Filter.mem_of_superset this ?_
    rw [closure_image_coe_ofPred_restrict_lt]
    intro x hx
    have e : embedding γ'.1 = embedding γ.1 := embedding_valueGroup₀ExtensionEquiv_symm v γ.1
    exact (v.extension.restrict_lt_iff_lt_embedding).2 (lt_of_lt_of_eq hx e)
