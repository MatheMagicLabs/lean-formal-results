/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     MeasureTheory.Filtration.limitProcess_smul
Source:      Mathlib @ a02a63c2, Mathlib/Probability/Process/LimitProcess.lean, line 250
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  O2-repair-vs-resample, arm A, attempt 2, verified in round 0 (round 0 = first attempt)
Prover:      claude-opus-5-5
Setup:       Opus 5.5: arm B = one attempt plus up to 3 repair rounds with Lean error messages; arm A = 4 independent attempts (attempt k)
Check:       the proof replaced the human proof in the Mathlib file above; Lean reported
             0 errors and no `sorry`; sorry/admit/native_decide/search tactics were rejected.
-/

-- (context: the Mathlib file above this declaration)
@[to_fun limitProcess_fun_smul]
lemma limitProcess_smul [Zero E] {G : Type*} [GroupWithZero G] [MulActionWithZero G E]
    [ContinuousConstSMul G E] (X : ι → Ω → E) (c : G) :
    𝓕.limitProcess (c • X) P =ᵐ[P] c • 𝓕.limitProcess X P := by
  by_cases hc : c = 0
  · subst hc
    have h0 : (0 : G) • X = 0 := by
      ext t ω
      simp
    rw [h0]
    filter_upwards [limitProcess_zero (𝓕 := 𝓕) (P := P) (E := E)] with ω h
    simp [h]
  · by_cases hX : HasLimitProcess X 𝓕 P
    · exact hX.limitProcess_comp (continuous_const_smul c)
    · have hX' : ¬ HasLimitProcess (c • X) 𝓕 P := (hasLimitProcess_smul_iff₀ hc).not.2 hX
      have h1 : 𝓕.limitProcess (c • X) P = 0 := dif_neg hX'
      have h2 : 𝓕.limitProcess X P = 0 := dif_neg hX
      filter_upwards with ω
      simp [h1, h2]
