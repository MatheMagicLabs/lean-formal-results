/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     MeasureTheory.Filtration.limitProcess_congr
Source:      Mathlib @ a02a63c2, Mathlib/Probability/Process/LimitProcess.lean, line 199
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  O5-repair-sonnet, arm A, attempt 0, verified in round 0 (round 0 = first attempt)
Prover:      claude-sonnet-5-5
Setup:       Sonnet 5.5: arm B = repair loop; arm A = independent attempts
Check:       the proof replaced the human proof in the Mathlib file above; Lean reported
             0 errors and no `sorry`; sorry/admit/native_decide/search tactics were rejected.
-/

-- (context: the Mathlib file above this declaration)
@[gcongr]
lemma limitProcess_congr (hXY : X ≡ᵐ[P] Y) :
    𝓕.limitProcess X P =ᵐ[P] 𝓕.limitProcess Y P := by
  rcases isEmpty_or_nonempty ι with hι | hι
  · have : X = Y := funext fun t => isEmptyElim t
    subst this
    exact Filter.EventuallyEq.rfl
  · by_cases h : HasLimitProcess X 𝓕 P
    · have h' := h.congr hXY
      refine limitProcess_ae_eq (g := 𝓕.limitProcess Y P) stronglyMeasurable_limitProcess ?_
      filter_upwards [hXY, h'.ae_tendsto_limitProcess] with ω h1 h2
      simp_all
    · have h' : ¬ HasLimitProcess Y 𝓕 P := fun h2 => h (h2.congr hXY.symm)
      unfold limitProcess
      rw [dif_neg h, dif_neg h']
