/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     MeasureTheory.Filtration.limitProcess_smul
Source:      Mathlib @ a02a63c2, Mathlib/Probability/Process/LimitProcess.lean, line 250
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  O2-repair-vs-resample, arm A, attempt 0, verified in round 0 (round 0 = first attempt)
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
  rcases eq_or_ne c 0 with rfl | hc
  · rw [zero_smul, zero_smul]
    exact limitProcess_zero
  by_cases h : HasLimitProcess X 𝓕 P
  · exact h.limitProcess_comp (continuous_const_smul c)
  · have h' : ¬ HasLimitProcess (c • X) 𝓕 P := (hasLimitProcess_smul_iff₀ hc).not.2 h
    unfold limitProcess
    rw [dif_neg h', dif_neg h, smul_zero]
