/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     Valuation.hasBasis_nhds_coe_zero
Source:      Mathlib @ a02a63c2, Mathlib/Topology/Algebra/ValuativeRel/Completion.lean, line 430
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  O2-repair-vs-resample, arm A, attempt 2, verified in round 0 (round 0 = first attempt)
Prover:      claude-opus-5-5
Setup:       Opus 5.5: arm B = one attempt plus up to 3 repair rounds with Lean error messages; arm A = 4 independent attempts (attempt k)
Check:       the proof replaced the human proof in the Mathlib file above; Lean reported
             0 errors and no `sorry`; sorry/admit/native_decide/search tactics were rejected.
-/

-- (context: the Mathlib file above this declaration)
theorem hasBasis_nhds_coe_zero :
    (𝓝 (0 : Completion K)).HasBasis (fun _ ↦ True)
      fun γ : v.extension.ValueGroup₀ˣ ↦ {x | v.extension.restrict x < γ.1} := by
  have h0 : (𝓝 (0 : K)).HasBasis (fun _ ↦ True)
      fun γ : v.ValueGroup₀ˣ ↦ {x | v.restrict x < γ.1} :=
    ⟨fun s ↦ by simpa using v.mem_nhds_zero_iff s⟩
  have h1 := h0.hasBasis_of_isDenseInducing Completion.isDenseInducing_coe
  rw [Completion.coe_zero] at h1
  simp only [closure_image_coe_ofPred_restrict_lt] at h1
  refine h1.to_hasBasis
    (fun γ _ ↦ ⟨Units.map v.valueGroup₀ExtensionEquiv.toMonoidHom γ, trivial, fun x hx ↦ ?_⟩)
    (fun γ _ ↦ ⟨Units.map v.valueGroup₀ExtensionEquiv.symm.toMonoidHom γ, trivial,
      fun x hx ↦ ?_⟩)
  · simp only [Set.mem_setOf_eq] at hx ⊢
    rw [Valuation.restrict_lt_iff_lt_embedding] at hx
    simpa using hx
  · simp only [Set.mem_setOf_eq] at hx ⊢
    rw [Valuation.restrict_lt_iff_lt_embedding]
    simpa using hx
