/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     Real.le_sum_log_nat
Source:      Mathlib @ a02a63c2, Mathlib/Analysis/SpecialFunctions/Log/Sum.lean, line 92
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  A1-astra, arm N3, verified in round 0 (round 0 = first attempt)
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
  | succ N ih =>
      have hset : Ioc 0 (N + 1) = insert (N + 1) (Ioc 0 N) := by
        ext k
        simp only [mem_Ioc, mem_insert]
        omega
      rw [hset, sum_insert (by simp)]
      by_cases hN : N = 0
      · subst N
        norm_num
      have hn : (0 : ℝ) < N :=
        Nat.cast_pos.mpr (Nat.pos_of_ne_zero hN)
      have h := log_le_sub_one_of_pos
        (show 0 < ((N : ℝ) + 1) / (N : ℝ) by positivity)
      rw [log_div (by positivity) (ne_of_gt hn)] at h
      have hb : (N : ℝ) * (log ((N : ℝ) + 1) - log N) ≤ 1 := by
        have hm := mul_le_mul_of_nonneg_left h (le_of_lt hn)
        have he : (N : ℝ) * (((N : ℝ) + 1) / (N : ℝ) - 1) = 1 := by
          field_simp [ne_of_gt hn] <;> ring
        rw [he] at hm
        exact hm
      simp only [Nat.cast_add, Nat.cast_one]
      nlinarith
