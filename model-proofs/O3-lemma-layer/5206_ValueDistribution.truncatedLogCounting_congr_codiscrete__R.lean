/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     ValueDistribution.truncatedLogCounting_congr_codiscrete
Source:      Mathlib @ a02a63c2, Mathlib/Analysis/Complex/ValueDistribution/LogCounting/Truncated.lean, line 128
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  O3-lemma-layer, arm R, verified in round 2 (round 0 = first attempt)
Prover:      claude-opus-5-5
Setup:       Opus 5.5 with repair loop: arm R = repair only; arm RS = repair plus the Lean-checked lemma layer
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
  have h1 : ∀ a : E, (fun z => f z - a) =ᶠ[codiscrete ℂ] (fun z => g z - a) := fun a => by
    filter_upwards [hfg] with z hz
    simp [hz]
  have h2 : ∀ a : E, MeromorphicOn.divisor (fun z => f z - a) univ
      = MeromorphicOn.divisor (fun z => g z - a) univ := fun a => by
    apply MeromorphicOn.divisor_congr_codiscreteWithin <;>
      first | exact h1 a | exact isOpen_univ
  have h3 : MeromorphicOn.divisor f univ = MeromorphicOn.divisor g univ := by
    apply MeromorphicOn.divisor_congr_codiscreteWithin <;>
      first | exact hfg | exact isOpen_univ
  funext a
  cases a <;> simp [truncatedLogCounting, h2, h3]
