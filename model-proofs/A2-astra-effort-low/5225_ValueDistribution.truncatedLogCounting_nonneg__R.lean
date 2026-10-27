/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     ValueDistribution.truncatedLogCounting_nonneg
Source:      Mathlib @ a02a63c2, Mathlib/Analysis/Complex/ValueDistribution/LogCounting/Truncated.lean, line 108
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  A2-astra-effort-low, arm R, verified in round 2 (round 0 = first attempt)
Prover:      gpt-6-astra
Setup:       GPT-6 Astra, reasoning effort low (arms R, N0)
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

theorem truncatedLogCounting_nonneg {r : ℝ} (hr : 1 ≤ r) :
    0 ≤ truncatedLogCounting f a r := by
  cases a <;>
    simp only [truncatedLogCounting_top, truncatedLogCounting_coe] <;>
    apply locallyFinsuppWithin.logCounting_nonneg <;>
    first
    | exact hr
    | simpa [locallyFinsuppWithin.truncate₁] using
        (show 0 ≤ (1 : ℤ) by norm_num)
    | intro z
      simp [locallyFinsuppWithin.truncate₁]
