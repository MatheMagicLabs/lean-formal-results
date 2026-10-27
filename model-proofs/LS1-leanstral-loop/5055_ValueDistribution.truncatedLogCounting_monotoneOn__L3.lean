/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     ValueDistribution.truncatedLogCounting_monotoneOn
Source:      Mathlib @ a02a63c2, Mathlib/Analysis/Complex/ValueDistribution/LogCounting/Truncated.lean, line 114
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  LS1-leanstral-loop, arm L3, verified in round 0 (round 0 = first attempt)
Prover:      labs-leanstral-1-5
Setup:       Leanstral 1.5 in a fixed check-and-repair loop: L1 = 1 candidate per round, L3 = up to 3
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
  intro x hx y hy hxy
  cases a with
  | top =>
      rw [truncatedLogCounting_top]
      have hD : 0 ≤ ((divisor f Set.univ)⁻.truncate₁) := by
        have hneg : 0 ≤ (divisor f Set.univ)⁻ := negPart_nonneg _
        exact truncate_nonneg 1 _ hneg
      exact logCounting_mono hD hx hy hxy
  | coe a₀ =>
      rw [truncatedLogCounting_coe]
      have hD : 0 ≤ ((divisor (f · - a₀) Set.univ)⁺.truncate₁) := by
        have hpos : 0 ≤ (divisor (f · - a₀) Set.univ)⁺ := posPart_nonneg _
        exact truncate_nonneg 1 _ hpos
      exact logCounting_mono hD hx hy hxy
