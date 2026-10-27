/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     Real.le_sum_log_nat
Source:      Mathlib @ a02a63c2, Mathlib/Analysis/SpecialFunctions/Log/Sum.lean, line 92
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  O3-lemma-layer, arm R, verified in round 0 (round 0 = first attempt)
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
  induction N with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_Ioc_succ_top (Nat.zero_le n)]
    have key : (n:ℝ) * (log (n+1) - log n) ≤ 1 := by
      rcases Nat.eq_zero_or_pos n with h | h
      · subst h; simp
      · have hn : (0:ℝ) < n := by exact_mod_cast h
        have h1 := Real.log_le_sub_one_of_pos (show (0:ℝ) < (n+1)/n by positivity)
        rw [Real.log_div (by positivity) hn.ne'] at h1
        have : ((n:ℝ)+1)/n - 1 = 1/n := by
          rw [div_sub_one hn.ne']
          congr 1
          ring
        rw [this] at h1
        calc (n:ℝ) * (log (n+1) - log n) ≤ n * (1/n) := by gcongr
          _ = 1 := mul_one_div_cancel hn.ne'
    push_cast
    nlinarith [key, ih]
