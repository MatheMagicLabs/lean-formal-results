/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     Real.le_sum_log_nat
Source:      Mathlib @ a02a63c2, Mathlib/Analysis/SpecialFunctions/Log/Sum.lean, line 92
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  A1-astra, arm R, verified in round 0 (round 0 = first attempt)
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
      by_cases hn : n = 0
      · subst n
        norm_num
      have hpos : (0 : ℝ) < n := by
        exact_mod_cast Nat.pos_of_ne_zero hn
      have hnext : (0 : ℝ) < (n : ℝ) + 1 := by positivity
      have hlog := log_le_sub_one_of_pos (div_pos hnext hpos)
      rw [log_div (ne_of_gt hnext) (ne_of_gt hpos)] at hlog
      have hmul := mul_le_mul_of_nonneg_left hlog (le_of_lt hpos)
      have hcancel :
          (n : ℝ) * (((n : ℝ) + 1) / (n : ℝ) - 1) = 1 := by
        field_simp
        <;> ring
      rw [hcancel] at hmul
      have hs :
          (∑ k ∈ Ioc 0 (n + 1), log (k : ℝ)) =
            (∑ k ∈ Ioc 0 n, log (k : ℝ)) + log (n + 1 : ℕ) := by
        rw [show Ioc 0 (n + 1) = insert (n + 1) (Ioc 0 n) by
          ext k
          simp only [mem_Ioc, mem_insert]
          omega]
        rw [sum_insert (by simp)]
        ring
      rw [hs]
      simp only [Nat.cast_add, Nat.cast_one]
      nlinarith
