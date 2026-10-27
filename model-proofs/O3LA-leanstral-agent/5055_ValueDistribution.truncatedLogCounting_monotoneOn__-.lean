/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     ValueDistribution.truncatedLogCounting_monotoneOn
Source:      Mathlib @ a02a63c2, Mathlib/Analysis/Complex/ValueDistribution/LogCounting/Truncated.lean, line 114
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  O3LA-leanstral-agent, arm -, verified in final
Prover:      labs-leanstral-1-5
Setup:       Leanstral 1.5 as a tool-using agent (Mistral Vibe)
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

theorem truncatedLogCounting_monotoneOn :
    MonotoneOn (truncatedLogCounting f a) (Set.Ioi 0) := by
  cases a with
  | top =>
    rw [truncatedLogCounting_top]
    exact locallyFinsuppWithin.logCounting_mono (truncate_nonneg 1 _ (negPart_nonneg _))
  | coe a₀ =>
    rw [truncatedLogCounting_coe]
    exact locallyFinsuppWithin.logCounting_mono (truncate_nonneg 1 _ (posPart_nonneg _))
