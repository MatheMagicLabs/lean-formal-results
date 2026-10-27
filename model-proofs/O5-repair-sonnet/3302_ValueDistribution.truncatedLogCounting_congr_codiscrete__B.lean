/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     ValueDistribution.truncatedLogCounting_congr_codiscrete
Source:      Mathlib @ a02a63c2, Mathlib/Analysis/Complex/ValueDistribution/LogCounting/Truncated.lean, line 128
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  O5-repair-sonnet, arm B, verified in round 2 (round 0 = first attempt)
Prover:      claude-sonnet-5-5
Setup:       Sonnet 5.5: arm B = repair loop; arm A = independent attempts
Check:       the proof replaced the human proof in the Mathlib file above; Lean reported
             0 errors and no `sorry`; sorry/admit/native_decide/search tactics were rejected.
-/

-- (context: the Mathlib file above this declaration)
theorem truncatedLogCounting_congr_codiscrete [NormedSpace ℂ E] {f g : ℂ → E}
    (hfg : f =ᶠ[codiscrete ℂ] g) :
    truncatedLogCounting f = truncatedLogCounting g := by
  have hfg' : f =ᶠ[codiscreteWithin (Set.univ : Set ℂ)] g := hfg
  have hd : ∀ a₀ : E, divisor (f · - a₀) Set.univ = divisor (g · - a₀) Set.univ := by
    intro a₀
    have hh : (fun x => f x - a₀) =ᶠ[codiscreteWithin (Set.univ : Set ℂ)] (fun x => g x - a₀) := by
      filter_upwards [hfg'] with x hx
      simp [hx]
    have hev : ∀ x : ℂ, (fun y => f y - a₀) =ᶠ[nhdsWithin x {x}ᶜ] (fun y => g y - a₀) := by
      intro x
      have := disjoint_principal_right.1 (mem_codiscreteWithin.1 hh x (Set.mem_univ x))
      filter_upwards [this] with y hy
      by_contra hne
      exact hy ⟨Set.mem_univ _, hne⟩
    by_cases hf : MeromorphicOn (fun x => f x - a₀) Set.univ
    · exact divisor_congr_codiscreteWithin_of_eqOn_compl hf hh
        (fun _ h => absurd (Set.mem_univ _) h)
    · have hg : ¬ MeromorphicOn (fun x => g x - a₀) Set.univ := by
        intro hg
        apply hf
        intro x hx
        exact (hg x hx).congr (hev x).symm
      first
      | (ext z; simp [MeromorphicOn.divisor, hf, hg]; done)
      | (simp [MeromorphicOn.divisor, hf, hg]; done)
      | (rw [MeromorphicOn.divisor_def, MeromorphicOn.divisor_def, dif_neg hf, dif_neg hg])
      | (ext z; simp [MeromorphicOn.divisor_apply, hf, hg]; done)
  funext a
  induction a using WithTop.recTopCoe with
  | top =>
    have := hd 0
    simp only [sub_zero] at this
    simp [truncatedLogCounting_top, this]
  | coe a₀ =>
    simp [truncatedLogCounting_coe, hd a₀]
