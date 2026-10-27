/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     Real.le_sum_log_nat
Source:      Mathlib @ a02a63c2, Mathlib/Analysis/SpecialFunctions/Log/Sum.lean, line 92
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  O3-lemma-layer, arm RS, verified in round 1 (round 0 = first attempt)
Prover:      claude-opus-5-5
Setup:       Opus 5.5 with repair loop: arm R = repair only; arm RS = repair plus the Lean-checked lemma layer
Check:       the proof replaced the human proof in the Mathlib file above; Lean reported
             0 errors and no `sorry`; sorry/admit/native_decide/search tactics were rejected.
-/

open Nat hiding log log_pos
open Finset intervalIntegral MeasureTheory
namespace Real
variable {x : ℝ} (N : ℕ)

theorem le_sum_log_nat : N * log N - N ≤ ∑ n ∈ Ioc 0 N, log n := by
  rw [sum_log_eq_log_factorial]
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · simp
  have hN' : (0:ℝ) < N := by exact_mod_cast hN
  have hf : (0:ℝ) < (N.factorial : ℝ) := by exact_mod_cast Nat.factorial_pos N
  have h := Real.pow_div_factorial_le_exp (N:ℝ) (Nat.cast_nonneg N) N
  have hpos : (0:ℝ) < (N:ℝ)^N / (N.factorial : ℝ) := div_pos (pow_pos hN' N) hf
  have := Real.log_le_log hpos h
  rw [Real.log_exp, Real.log_div (pow_pos hN' N).ne' hf.ne', Real.log_pow] at this
  linarith
