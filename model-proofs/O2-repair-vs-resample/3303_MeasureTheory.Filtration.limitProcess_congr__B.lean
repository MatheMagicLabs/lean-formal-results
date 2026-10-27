/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     MeasureTheory.Filtration.limitProcess_congr
Source:      Mathlib @ a02a63c2, Mathlib/Probability/Process/LimitProcess.lean, line 199
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  O2-repair-vs-resample, arm B, verified in round 0 (round 0 = first attempt)
Prover:      claude-opus-5-5
Setup:       Opus 5.5: arm B = one attempt plus up to 3 repair rounds with Lean error messages; arm A = 4 independent attempts (attempt k)
Check:       the proof replaced the human proof in the Mathlib file above; Lean reported
             0 errors and no `sorry`; sorry/admit/native_decide/search tactics were rejected.
-/

-- (context: the Mathlib file above this declaration)
@[gcongr]
lemma limitProcess_congr (hXY : X ≡ᵐ[P] Y) :
    𝓕.limitProcess X P =ᵐ[P] 𝓕.limitProcess Y P := by
  rcases isEmpty_or_nonempty ι with hι | hι
  · have : X = Y := funext fun t => isEmptyElim t
    rw [this]
  · by_cases h : HasLimitProcess X 𝓕 P
    · have hY := h.congr hXY
      refine limitProcess_ae_eq stronglyMeasurable_limitProcess ?_
      filter_upwards [hXY, hY.ae_tendsto_limitProcess] with ω h1 h2
      simpa [h1] using h2
    · have hY : ¬ HasLimitProcess Y 𝓕 P := fun h' => h (h'.congr hXY.symm)
      simp only [limitProcess, dif_neg h, dif_neg hY]
      exact Filter.EventuallyEq.rfl
