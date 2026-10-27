/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     MeasureTheory.Filtration.limitProcess_ae_eq
Source:      Mathlib @ a02a63c2, Mathlib/Probability/Process/LimitProcess.lean, line 191
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  O5-repair-haiku, arm A, attempt 3, verified in round 0 (round 0 = first attempt)
Prover:      claude-haiku-4-5
Setup:       Haiku 4.5: arm B = repair loop; arm A = independent attempts
Check:       the proof replaced the human proof in the Mathlib file above; Lean reported
             0 errors and no `sorry`; sorry/admit/native_decide/search tactics were rejected.
-/

-- (context: the Mathlib file above this declaration)
lemma limitProcess_ae_eq (mg : StronglyMeasurable[⨆ t, 𝓕 t] g)
    (hg : ∀ᵐ ω ∂P, Tendsto (X · ω) atTop (𝓝 (g ω))) :
    𝓕.limitProcess X P =ᵐ[P] g := by
  by_cases h : 𝓕.HasLimitProcess X P
  · rw [limitProcess, dite_eq_left h]
    have : ∀ᵐ ω ∂P, Tendsto (X · ω) atTop (𝓝 (h.choose ω)) := h.choose_spec.2
    filter_upwards [this, hg] with ω h_choose h_g
    exact tendsto_nhds_unique h_choose h_g
  · rw [limitProcess, dite_eq_right h]
    exfalso
    apply h
    exact ⟨g, mg, hg⟩
