/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     ValueDistribution.truncatedLogCounting_congr_codiscrete
Source:      Mathlib @ a02a63c2, Mathlib/Analysis/Complex/ValueDistribution/LogCounting/Truncated.lean, line 128
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  O2-repair-vs-resample, arm B, verified in round 0 (round 0 = first attempt)
Prover:      claude-opus-5-5
Setup:       Opus 5.5: arm B = one attempt plus up to 3 repair rounds with Lean error messages; arm A = 4 independent attempts (attempt k)
Check:       the proof replaced the human proof in the Mathlib file above; Lean reported
             0 errors and no `sorry`; sorry/admit/native_decide/search tactics were rejected.
-/

-- (context: the Mathlib file above this declaration)
theorem truncatedLogCounting_congr_codiscrete [NormedSpace ℂ E] {f g : ℂ → E}
    (hfg : f =ᶠ[codiscrete ℂ] g) :
    truncatedLogCounting f = truncatedLogCounting g := by
  have key : ∀ h₁ h₂ : ℂ → E, h₁ =ᶠ[codiscrete ℂ] h₂ →
      divisor h₁ univ = divisor h₂ univ := by
    intro h₁ h₂ h
    by_cases m₁ : MeromorphicOn h₁ univ
    · exact divisor_congr_codiscreteWithin_of_eqOn_compl m₁ h (by simp)
    by_cases m₂ : MeromorphicOn h₂ univ
    · exact (divisor_congr_codiscreteWithin_of_eqOn_compl m₂ h.symm (by simp)).symm
    simp [divisor, m₁, m₂]
  funext a
  induction a using WithTop.recTopCoe with
  | top => rw [truncatedLogCounting_top, truncatedLogCounting_top, key f g hfg]
  | coe a₀ =>
    have h' : (fun x => f x - a₀) =ᶠ[codiscrete ℂ] (fun x => g x - a₀) := by
      filter_upwards [hfg] with x hx
      simp [hx]
    rw [truncatedLogCounting_coe, truncatedLogCounting_coe, key _ _ h']
