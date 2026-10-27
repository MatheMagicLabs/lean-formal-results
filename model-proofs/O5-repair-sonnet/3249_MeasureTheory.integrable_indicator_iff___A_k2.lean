/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     MeasureTheory.integrable_indicator_iff₀
Source:      Mathlib @ a02a63c2, Mathlib/MeasureTheory/Integral/IntegrableOn.lean, line 334
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  O5-repair-sonnet, arm A, attempt 2, verified in round 0 (round 0 = first attempt)
Prover:      claude-sonnet-5-5
Setup:       Sonnet 5.5: arm B = repair loop; arm A = independent attempts
Check:       the proof replaced the human proof in the Mathlib file above; Lean reported
             0 errors and no `sorry`; sorry/admit/native_decide/search tactics were rejected.
-/

-- (context: the Mathlib file above this declaration)
theorem integrable_indicator_iff₀ (hs : NullMeasurableSet s μ) :
    Integrable (indicator s f) μ ↔ IntegrableOn f s μ := by
  constructor
  · intro h
    refine (h.integrableOn (s := s)).congr_fun_ae ?_
    rw [Filter.EventuallyEq, ae_restrict_iff'₀ hs]
    exact Eventually.of_forall fun x hx => indicator_of_mem hx f
  · intro h
    classical
    have := Integrable.piecewise hs h (integrableOn_zero (s := sᶜ) (μ := μ))
    refine this.congr (Eventually.of_forall fun x => ?_)
    by_cases hx : x ∈ s <;> simp [hx]
