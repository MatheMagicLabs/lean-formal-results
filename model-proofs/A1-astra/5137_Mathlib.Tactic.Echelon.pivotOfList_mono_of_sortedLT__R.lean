/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     Mathlib.Tactic.Echelon.pivotOfList_mono_of_sortedLT
Source:      Mathlib @ a02a63c2, Mathlib/Tactic/Echelon/Reflection.lean, line 122
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  A1-astra, arm R, verified in round 2 (round 0 = first attempt)
Prover:      gpt-6-astra
Setup:       GPT-6 Astra (Codex, effort medium): R = proof plus up to 3 repair rounds with Lean errors; RS = R plus lemma layer; RT = R with read-only Mathlib sources to search; N0-N3 = independent attempts
Check:       the proof replaced the human proof in the Mathlib file above; Lean reported
             0 errors and no `sorry`; sorry/admit/native_decide/search tactics were rejected.
-/

open Mathlib.Tactic.Matrix
namespace Mathlib.Tactic.Echelon
variable {α : Type*}
variable {n : ℕ}

theorem pivotOfList_mono_of_sortedLT {cols : List (Fin n)} (hsorted : cols.SortedLT) :
    Monotone (pivotOfList cols) := by
  have hp : cols.Pairwise (· < ·) :=
    List.sortedLT_iff_pairwise.mp hsorted
  clear hsorted
  induction cols with
  | nil =>
      intro i j hij
      simp only [pivotOfList]
      exact le_rfl
  | cons a cols ih =>
      obtain ⟨ha, ht⟩ := List.pairwise_cons.mp hp
      have hm := ih ht
      have hzero : pivotOfList (a :: cols) 0 ≤ pivotOfList cols 0 := by
        cases cols with
        | nil =>
            change (a : WithTop (Fin n)) ≤ ⊤
            exact le_top
        | cons b bs =>
            change (a : WithTop (Fin n)) ≤ (b : WithTop (Fin n))
            exact WithTop.coe_le_coe.mpr (ha b (by simp)).le
      intro i j hij
      cases i with
      | zero =>
          cases j with
          | zero => exact le_rfl
          | succ j =>
              simpa [pivotOfList] using
                hzero.trans (hm (Nat.zero_le j))
      | succ i =>
          cases j with
          | zero => omega
          | succ j =>
              simpa [pivotOfList] using
                hm (Nat.le_of_succ_le_succ hij)
