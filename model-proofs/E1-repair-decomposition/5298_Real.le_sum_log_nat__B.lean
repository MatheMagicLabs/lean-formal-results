/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     Real.le_sum_log_nat
Source:      Mathlib @ a02a63c2, Mathlib/Analysis/SpecialFunctions/Log/Sum.lean, line 92
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  E1-repair-decomposition, arm B, verified in round 0 (round 0 = first attempt)
Prover:      gpt-6-astra
Setup:       GPT-6 Astra, which part of Lean feedback makes repair work: after a shared first attempt (E0), V = full error messages, Z = line numbers only, B = only "Lean rejected this proof"
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
        simp
      have hp : 0 < (n : ℝ) := by
        exact_mod_cast Nat.pos_of_ne_zero hn
      have hs : 0 < (n : ℝ) + 1 := by positivity
      have hlog :=
        log_le_sub_one_of_pos (div_pos hs hp)
      rw [log_div (ne_of_gt hs) (ne_of_gt hp)] at hlog
      have hmul := mul_le_mul_of_nonneg_left hlog (le_of_lt hp)
      have he : (n : ℝ) * (((n : ℝ) + 1) / n - 1) = 1 := by
        field_simp [ne_of_gt hp] <;> ring
      rw [he] at hmul
      have hI : Ioc 0 (n + 1) = insert (n + 1) (Ioc 0 n) := by
        ext k
        simp only [mem_Ioc, mem_insert]
        omega
      rw [hI, sum_insert (by simp)]
      simp only [Nat.cast_add, Nat.cast_one]
      nlinarith
