/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     MeasureTheory.Filtration.limitProcess_congr
Source:      Mathlib @ a02a63c2, Mathlib/Probability/Process/LimitProcess.lean, line 199
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  O5-repair-sonnet, arm A, attempt 3, verified in round 0 (round 0 = first attempt)
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
  · have hXY : X = Y := Subsingleton.elim _ _
    subst hXY
    exact EventuallyEq.rfl
  · by_cases hX : HasLimitProcess X 𝓕 P
    · have hY := hX.congr hXY
      have h1 := hX.ae_tendsto_limitProcess
      have h2 := hY.ae_tendsto_limitProcess
      filter_upwards [hXY, h1, h2] with ω hω h1 h2
      have h3 : Tendsto (Y · ω) atTop (𝓝 (𝓕.limitProcess X P ω)) := by
        clear h2
        simp_all
      exact tendsto_nhds_unique h3 h2
    · have hY : ¬ HasLimitProcess Y 𝓕 P := fun h' => hX (h'.congr hXY.symm)
      have e1 : 𝓕.limitProcess X P = 0 := dif_neg hX
      have e2 : 𝓕.limitProcess Y P = 0 := dif_neg hY
      filter_upwards with ω
      simp [e1, e2]
