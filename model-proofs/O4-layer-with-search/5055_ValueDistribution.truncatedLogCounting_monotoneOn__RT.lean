/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     ValueDistribution.truncatedLogCounting_monotoneOn
Source:      Mathlib @ a02a63c2, Mathlib/Analysis/Complex/ValueDistribution/LogCounting/Truncated.lean, line 114
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  O4-layer-with-search, arm RT, verified in round 0 (round 0 = first attempt)
Prover:      claude-opus-5-5
Setup:       Opus 5.5 with repair loop, lemma layer and name search (arm RT)
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
  induction a using WithTop.recTopCoe with
  | top =>
    rw [truncatedLogCounting_top]
    apply logCounting_mono
    intro x
    first
      | simp [truncate₁]
      | (simp only [truncate₁]; positivity)
      | (simp [truncate₁]; split_ifs <;> simp_all <;> omega)
      | (simp [truncate₁]; omega)
  | coe a₀ =>
    rw [truncatedLogCounting_coe]
    apply logCounting_mono
    intro x
    first
      | simp [truncate₁]
      | (simp only [truncate₁]; positivity)
      | (simp [truncate₁]; split_ifs <;> simp_all <;> omega)
      | (simp [truncate₁]; omega)
