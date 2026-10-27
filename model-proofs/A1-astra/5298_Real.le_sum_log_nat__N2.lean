/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     Real.le_sum_log_nat
Source:      Mathlib @ a02a63c2, Mathlib/Analysis/SpecialFunctions/Log/Sum.lean, line 92
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  A1-astra, arm N2, verified in round 0 (round 0 = first attempt)
Prover:      gpt-6-astra
Setup:       GPT-6 Astra (Codex, effort medium): R = proof plus up to 3 repair rounds with Lean errors; RS = R plus lemma layer; RT = R with read-only Mathlib sources to search; N0-N3 = independent attempts
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
      have hset : Ioc 0 (n + 1) = insert (n + 1) (Ioc 0 n) := by
        ext k
        simp only [mem_Ioc, mem_insert]
        omega
      rw [hset, sum_insert (by simp)]
      simp only [Nat.cast_add, Nat.cast_one]
      by_cases hn : n = 0
      · subst n
        simp
      · have hn0 : (0 : ℝ) < n := by
          exact_mod_cast Nat.pos_of_ne_zero hn
        have hlog := log_le_sub_one_of_pos
          (show 0 < ((n : ℝ) + 1) / n by positivity)
        rw [log_div (by positivity) (ne_of_gt hn0)] at hlog
        have hdiv : (n : ℝ) * (((n : ℝ) + 1) / n - 1) = 1 := by
          field_simp [ne_of_gt hn0] <;> ring
        have hstep :
            (n : ℝ) * (log ((n : ℝ) + 1) - log n) ≤ 1 := by
          have h := mul_le_mul_of_nonneg_left hlog hn0.le
          rw [hdiv] at h
          exact h
        nlinarith
