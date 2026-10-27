/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     Mathlib.Tactic.Echelon.pivotOfList_lt_pivotOfList
Source:      Mathlib @ a02a63c2, Mathlib/Tactic/Echelon/Reflection.lean, line 117
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  O3-lemma-layer, arm R, verified in round 1 (round 0 = first attempt)
Prover:      claude-opus-5-5
Setup:       Opus 5.5 with repair loop: arm R = repair only; arm RS = repair plus the Lean-checked lemma layer
Check:       the proof replaced the human proof in the Mathlib file above; Lean reported
             0 errors and no `sorry`; sorry/admit/native_decide/search tactics were rejected.
-/

open Mathlib.Tactic.Matrix
namespace Mathlib.Tactic.Echelon
variable {α : Type*}
variable {n : ℕ}

theorem pivotOfList_lt_pivotOfList {cols : List (Fin n)} (hsorted : cols.SortedLT) {i j : ℕ}
    (hij : i < j) (hj : pivotOfList cols j ≠ ⊤) : pivotOfList cols i < pivotOfList cols j := by
  have hjlen : j < cols.length := by
    by_contra h
    apply hj
    simp [pivotOfList, List.getElem?_eq_none (by omega : cols.length ≤ j)]
    all_goals rfl
  have hilen : i < cols.length := by omega
  have hp : cols.Pairwise (· < ·) := by
    first
      | exact hsorted.pairwise
      | exact List.sortedLT_iff_pairwise.mp hsorted
      | simpa [List.SortedLT] using hsorted
      | exact hsorted
      | simpa [List.SortedLT, List.Sorted] using hsorted
  have hlt := List.pairwise_iff_getElem.mp hp i j hilen hjlen hij
  simp [pivotOfList, List.getElem?_eq_getElem hilen, List.getElem?_eq_getElem hjlen]
  all_goals first
    | exact WithTop.coe_lt_coe.mpr hlt
    | exact WithTop.some_lt_some.mpr hlt
    | exact Option.some_lt_some.mpr hlt
