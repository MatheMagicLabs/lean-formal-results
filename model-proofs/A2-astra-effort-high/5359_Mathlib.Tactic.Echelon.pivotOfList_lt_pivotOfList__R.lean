/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     Mathlib.Tactic.Echelon.pivotOfList_lt_pivotOfList
Source:      Mathlib @ a02a63c2, Mathlib/Tactic/Echelon/Reflection.lean, line 117
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  A2-astra-effort-high, arm R, verified in round 3 (round 0 = first attempt)
Prover:      gpt-6-astra
Setup:       GPT-6 Astra, reasoning effort high (arms R, N0)
Check:       the proof replaced the human proof in the Mathlib file above; Lean reported
             0 errors and no `sorry`; sorry/admit/native_decide/search tactics were rejected.
-/

open Mathlib.Tactic.Matrix
namespace Mathlib.Tactic.Echelon
variable {α : Type*}
variable {n : ℕ}

theorem pivotOfList_lt_pivotOfList {cols : List (Fin n)} (hsorted : cols.SortedLT) {i j : ℕ}
    (hij : i < j) (hj : pivotOfList cols j ≠ ⊤) : pivotOfList cols i < pivotOfList cols j := by
  revert hsorted i j
  induction cols with
  | nil =>
      intro hsorted i j hij hj
      simp [pivotOfList] at hj
      exact (hj rfl).elim
  | cons a cols ih =>
      intro hsorted i j hij hj
      have hs : (∀ b ∈ cols, a < b) ∧ cols.SortedLT := by
        simpa using hsorted
      have htail : cols.SortedLT := hs.2
      cases j with
      | zero => omega
      | succ j =>
          cases i with
          | zero =>
              cases cols with
              | nil =>
                  simp [pivotOfList] at hj
                  exact (hj rfl).elim
              | cons b cols =>
                  have hab : a < b := hs.1 b (by simp)
                  cases j with
                  | zero =>
                      change (a : WithTop (Fin n)) < (b : WithTop (Fin n))
                      exact WithTop.coe_lt_coe.mpr hab
                  | succ j =>
                      have hj' : pivotOfList (b :: cols) (j + 1) ≠ ⊤ := by
                        simpa [pivotOfList] using hj
                      have hnext := ih htail (Nat.zero_lt_succ j) hj'
                      have hfirst :
                          pivotOfList (a :: b :: cols) 0 <
                            pivotOfList (b :: cols) 0 := by
                        change (a : WithTop (Fin n)) < (b : WithTop (Fin n))
                        exact WithTop.coe_lt_coe.mpr hab
                      simpa [pivotOfList] using lt_trans hfirst hnext
          | succ i =>
              have hj' : pivotOfList cols j ≠ ⊤ := by
                simpa [pivotOfList] using hj
              simpa [pivotOfList] using
                ih htail (Nat.lt_of_succ_lt_succ hij) hj'
