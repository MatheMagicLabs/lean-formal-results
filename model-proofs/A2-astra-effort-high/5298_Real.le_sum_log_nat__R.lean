/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     Real.le_sum_log_nat
Source:      Mathlib @ a02a63c2, Mathlib/Analysis/SpecialFunctions/Log/Sum.lean, line 92
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  A2-astra-effort-high, arm R, verified in round 0 (round 0 = first attempt)
Prover:      gpt-6-astra
Setup:       GPT-6 Astra, reasoning effort high (arms R, N0)
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
    have hI : Ioc 0 (n + 1) = insert (n + 1) (Ioc 0 n) := by
      ext k
      simp only [mem_Ioc, mem_insert]
      omega
    rw [hI, sum_insert (by simp)]
    by_cases hn : n = 0
    · subst n
      simp
    have hnpos : (0 : ℝ) < n := by
      exact_mod_cast Nat.pos_of_ne_zero hn
    have hratio : 0 < ((n : ℝ) + 1) / (n : ℝ) :=
      div_pos (by positivity) hnpos
    have hlog := log_le_sub_one_of_pos hratio
    rw [log_div (by positivity) (ne_of_gt hnpos)] at hlog
    have hmul := mul_le_mul_of_nonneg_left hlog (le_of_lt hnpos)
    have hcancel :
        (n : ℝ) * (((n : ℝ) + 1) / (n : ℝ) - 1) = 1 := by
      field_simp [ne_of_gt hnpos] <;> ring
    rw [hcancel] at hmul
    simp only [Nat.cast_succ, Nat.cast_add, Nat.cast_one]
    nlinarith
