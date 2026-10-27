/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     ValueDistribution.truncatedLogCounting_le
Source:      Mathlib @ a02a63c2, Mathlib/Analysis/Complex/ValueDistribution/LogCounting/Truncated.lean, line 102
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  E1-repair-decomposition, arm V, verified in round 0 (round 0 = first attempt)
Prover:      gpt-6-astra
Setup:       GPT-6 Astra, which part of Lean feedback makes repair work: after a shared first attempt (E0), V = full error messages, Z = line numbers only, B = only "Lean rejected this proof"
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

theorem truncatedLogCounting_le {r : ℝ} (hr : 1 ≤ r) :
    truncatedLogCounting f a r ≤ logCounting f a r := by
  cases a <;>
    simp only [truncatedLogCounting_top, truncatedLogCounting_coe,
      logCounting_top, logCounting_coe]
  all_goals
    apply Function.locallyFinsuppWithin.logCounting_mono hr
    intro z
    simp
