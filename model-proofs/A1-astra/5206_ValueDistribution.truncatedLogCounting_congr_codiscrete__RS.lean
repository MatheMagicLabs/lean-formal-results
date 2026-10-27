/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     ValueDistribution.truncatedLogCounting_congr_codiscrete
Source:      Mathlib @ a02a63c2, Mathlib/Analysis/Complex/ValueDistribution/LogCounting/Truncated.lean, line 128
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  A1-astra, arm RS, verified in round 3 (round 0 = first attempt)
Prover:      gpt-6-astra
Setup:       GPT-6 Astra (Codex, effort medium): R = proof plus up to 3 repair rounds with Lean errors; RS = R plus lemma layer; RT = R with read-only Mathlib sources to search; N0-N3 = independent attempts
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
  have hd : ∀ {u v : ℂ → E}, u =ᶠ[codiscrete ℂ] v →
      divisor u univ = divisor v univ := by
    intro u v huv
    have huv' : u =ᶠ[codiscreteWithin (univ : Set ℂ)] v := by
      simpa [codiscreteWithin, codiscrete] using huv
    exact divisor_congr_codiscreteWithin huv' isOpen_univ
  funext a
  induction a using WithTop.recTopCoe with
  | top =>
      simp only [truncatedLogCounting_top, hd hfg]
  | coe a =>
      have ha : (fun z => f z - a) =ᶠ[codiscrete ℂ] (fun z => g z - a) :=
        hfg.sub (Filter.EventuallyEq.refl _ _)
      simp only [truncatedLogCounting_coe, hd ha]
