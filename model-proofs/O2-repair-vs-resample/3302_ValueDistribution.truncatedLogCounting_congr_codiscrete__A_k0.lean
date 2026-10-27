/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     ValueDistribution.truncatedLogCounting_congr_codiscrete
Source:      Mathlib @ a02a63c2, Mathlib/Analysis/Complex/ValueDistribution/LogCounting/Truncated.lean, line 128
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  O2-repair-vs-resample, arm A, attempt 0, verified in round 0 (round 0 = first attempt)
Prover:      claude-opus-5-5
Setup:       Opus 5.5: arm B = one attempt plus up to 3 repair rounds with Lean error messages; arm A = 4 independent attempts (attempt k)
Check:       the proof replaced the human proof in the Mathlib file above; Lean reported
             0 errors and no `sorry`; sorry/admit/native_decide/search tactics were rejected.
-/

-- (context: the Mathlib file above this declaration)
theorem truncatedLogCounting_congr_codiscrete [NormedSpace ℂ E] {f g : ℂ → E}
    (hfg : f =ᶠ[codiscrete ℂ] g) :
    truncatedLogCounting f = truncatedLogCounting g := by
  have key : ∀ f₁ f₂ : ℂ → E, f₁ =ᶠ[codiscrete ℂ] f₂ →
      divisor f₁ Set.univ = divisor f₂ Set.univ := by
    intro f₁ f₂ h
    by_cases hf : MeromorphicOn f₁ Set.univ
    · exact divisor_congr_codiscreteWithin_of_eqOn_compl hf h (fun x hx => by simp at hx)
    · have hg : ¬ MeromorphicOn f₂ Set.univ := fun hg =>
        hf (hg.congr_codiscreteWithin h.symm isOpen_univ)
      ext z
      simp [divisor_def, hf, hg]
  funext a
  induction a using WithTop.recTopCoe with
  | top =>
    rw [truncatedLogCounting_top, truncatedLogCounting_top, key f g hfg]
  | coe a₀ =>
    rw [truncatedLogCounting_coe, truncatedLogCounting_coe,
      key (f · - a₀) (g · - a₀) (hfg.mono fun x hx => by simp [hx])]
