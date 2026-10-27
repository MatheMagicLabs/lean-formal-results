/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     Valuation.hasBasis_nhds_coe_zero
Source:      Mathlib @ a02a63c2, Mathlib/Topology/Algebra/ValuativeRel/Completion.lean, line 430
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  O2-repair-vs-resample, arm A, attempt 1, verified in round 0 (round 0 = first attempt)
Prover:      claude-opus-5-5
Setup:       Opus 5.5: arm B = one attempt plus up to 3 repair rounds with Lean error messages; arm A = 4 independent attempts (attempt k)
Check:       the proof replaced the human proof in the Mathlib file above; Lean reported
             0 errors and no `sorry`; sorry/admit/native_decide/search tactics were rejected.
-/

-- (context: the Mathlib file above this declaration)
theorem hasBasis_nhds_coe_zero :
    (𝓝 (0 : Completion K)).HasBasis (fun _ ↦ True)
      fun γ : v.extension.ValueGroup₀ˣ ↦ {x | v.extension.restrict x < γ.1} := by
  have h := v.hasBasis_nhds_zero.hasBasis_of_isDenseInducing Completion.isDenseInducing_coe
  rw [Completion.coe_zero] at h
  refine h.to_hasBasis
    (fun γ _ ↦ ⟨Units.map v.valueGroup₀ExtensionEquiv.toMonoidHom γ, trivial, ?_⟩)
    (fun γ _ ↦ ⟨Units.map v.valueGroup₀ExtensionEquiv.symm.toMonoidHom γ, trivial, ?_⟩)
  · intro x hx
    refine (Set.ext_iff.mp (v.closure_image_coe_ofPred_restrict_lt γ) x).mpr ?_
    simp only [Set.mem_setOf_eq, Valuation.restrict_lt_iff_lt_embedding] at hx ⊢
    simpa using hx
  · intro x hx
    have hx' := (Set.ext_iff.mp (v.closure_image_coe_ofPred_restrict_lt _) x).mp hx
    simp only [Set.mem_setOf_eq, Valuation.restrict_lt_iff_lt_embedding] at hx' ⊢
    simpa using hx'
