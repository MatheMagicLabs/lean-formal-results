/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     Valuation.hasBasis_nhds_coe_zero
Source:      Mathlib @ a02a63c2, Mathlib/Topology/Algebra/ValuativeRel/Completion.lean, line 430
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  O5-repair-sonnet, arm A, attempt 2, verified in round 0 (round 0 = first attempt)
Prover:      claude-sonnet-5-5
Setup:       Sonnet 5.5: arm B = repair loop; arm A = independent attempts
Check:       the proof replaced the human proof in the Mathlib file above; Lean reported
             0 errors and no `sorry`; sorry/admit/native_decide/search tactics were rejected.
-/

-- (context: the Mathlib file above this declaration)
theorem hasBasis_nhds_coe_zero :
    (𝓝 (0 : Completion K)).HasBasis (fun _ ↦ True)
      fun γ : v.extension.ValueGroup₀ˣ ↦ {x | v.extension.restrict x < γ.1} := by
  have key : ∀ γ : v.ValueGroup₀ˣ, closure ((↑) '' {x : K | v.restrict x < γ.1}) =
      {x : Completion K | v.extension.restrict x < v.valueGroup₀ExtensionEquiv γ.1} := by
    intro γ
    rw [closure_image_coe_ofPred_restrict_lt]
    ext x
    simp only [Set.mem_setOf_eq, restrict_lt_iff_lt_embedding,
      embedding_valueGroup₀ExtensionEquiv]
  have h := (v.hasBasis_nhds_zero).hasBasis_of_isDenseInducing
    (Completion.isDenseInducing_coe (α := K))
  rw [Completion.coe_zero] at h
  refine h.to_hasBasis (fun γ _ ↦ ?_) (fun γ' _ ↦ ?_)
  · refine ⟨Units.map (v.valueGroup₀ExtensionEquiv : v.ValueGroup₀ →* v.extension.ValueGroup₀) γ,
      trivial, ?_⟩
    exact (key γ).symm.subset
  · refine ⟨Units.map (v.valueGroup₀ExtensionEquiv.symm :
      v.extension.ValueGroup₀ →* v.ValueGroup₀) γ', trivial, ?_⟩
    intro x hx
    have hx' := (key (Units.map (v.valueGroup₀ExtensionEquiv.symm :
      v.extension.ValueGroup₀ →* v.ValueGroup₀) γ')).subset hx
    simpa using hx'
