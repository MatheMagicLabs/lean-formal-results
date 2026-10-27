/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     ValueDistribution.truncatedLogCounting_congr_codiscrete
Source:      Mathlib @ a02a63c2, Mathlib/Analysis/Complex/ValueDistribution/LogCounting/Truncated.lean, line 128
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  A2-astra-effort-high, arm R, verified in round 2 (round 0 = first attempt)
Prover:      gpt-6-astra
Setup:       GPT-6 Astra, reasoning effort high (arms R, N0)
Check:       the proof replaced the human proof in the Mathlib file above; Lean reported
             0 errors and no `sorry`; sorry/admit/native_decide/search tactics were rejected.
-/

open Filter Function MeromorphicOn Metric Real Set
namespace Function.locallyFinsuppWithin
variable {E : Type*} [NormedAddCommGroup E] [ProperSpace E]
end Function.locallyFinsuppWithin
namespace ValueDistribution
open locallyFinsuppWithin
variable
variable (f a) in
attribute [local simp] truncatedLogCounting_top truncatedLogCounting_coe

theorem truncatedLogCounting_congr_codiscrete [NormedSpace ℂ E] {f g : ℂ → E}
    (hfg : f =ᶠ[codiscrete ℂ] g) :
    truncatedLogCounting f = truncatedLogCounting g := by
  have hdiv (u v : ℂ → E) (huv : u =ᶠ[codiscrete ℂ] v) :
      divisor u univ = divisor v univ := by
    apply divisor_congr_codiscreteWithin
    · simpa [codiscreteWithin, codiscrete] using huv
    · exact isOpen_univ
  funext a
  induction a using WithTop.recTopCoe with
  | top =>
      simp only [truncatedLogCounting_top, hdiv f g hfg]
  | coe a =>
      have hsub : (fun z => f z - a) =ᶠ[codiscrete ℂ] (fun z => g z - a) := by
        filter_upwards [hfg] with z hz
        rw [hz]
      simp only [truncatedLogCounting_coe, hdiv _ _ hsub]
