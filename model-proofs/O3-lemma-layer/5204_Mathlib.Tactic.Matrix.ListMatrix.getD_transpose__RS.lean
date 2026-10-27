/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     Mathlib.Tactic.Matrix.ListMatrix.getD_transpose
Source:      Mathlib @ a02a63c2, Mathlib/Tactic/Matrix/ListMatrix.lean, line 83
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  O3-lemma-layer, arm RS, verified in round 3 (round 0 = first attempt)
Prover:      claude-opus-5-5
Setup:       Opus 5.5 with repair loop: arm R = repair only; arm RS = repair plus the Lean-checked lemma layer
Check:       the proof replaced the human proof in the Mathlib file above; Lean reported
             0 errors and no `sorry`; sorry/admit/native_decide/search tactics were rejected.
-/

namespace Mathlib.Tactic.Matrix.ListMatrix
variable {α : Type*}

theorem getD_transpose [Zero α] {n j : Nat} (rows : List (List α)) (i : Nat) (hj : j < n) :
    ((transpose n rows).getD j []).getD i 0 = (rows.getD i []).getD j 0 := by
  induction rows generalizing i with
  | nil => simp [transpose, List.getElem?_replicate, hj]
  | cons row rows ih =>
    have hlen := length_transpose n rows
    have hj' : j < (List.zipWith List.cons (row.rightpad n 0) (transpose n rows)).length := by
      simp [List.rightpad, hlen] <;> omega
    have hj2 : j < (transpose n rows).length := by rw [hlen]; exact hj
    rw [transpose, consPad_eq_zipWith, length_transpose]
    simp only [List.getD_eq_getElem?_getD] at ih ⊢
    rw [List.getElem?_eq_getElem hj', Option.getD_some, List.getElem_zipWith]
    cases i with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.getD_some]
      simp only [List.rightpad]
      by_cases h : j < row.length
      · rw [List.getElem_append_left h, List.getElem?_eq_getElem h, Option.getD_some]
      · rw [List.getElem_append_right (by omega), List.getElem_replicate,
          List.getElem?_eq_none (by omega), Option.getD_none]
    | succ i =>
      simp only [List.getElem?_cons_succ]
      rw [← ih i, List.getElem?_eq_getElem hj2, Option.getD_some]
