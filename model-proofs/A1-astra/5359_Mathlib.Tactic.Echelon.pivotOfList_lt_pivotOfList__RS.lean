/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     Mathlib.Tactic.Echelon.pivotOfList_lt_pivotOfList
Source:      Mathlib @ a02a63c2, Mathlib/Tactic/Echelon/Reflection.lean, line 117
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  A1-astra, arm RS, verified in round 1 (round 0 = first attempt)
Prover:      gpt-6-astra
Setup:       GPT-6 Astra (Codex, effort medium): R = proof plus up to 3 repair rounds with Lean errors; RS = R plus lemma layer; RT = R with read-only Mathlib sources to search; N0-N3 = independent attempts
Check:       the proof replaced the human proof in the Mathlib file above; Lean reported
             0 errors and no `sorry`; sorry/admit/native_decide/search tactics were rejected.
-/

open Mathlib.Tactic.Matrix
namespace Mathlib.Tactic.Echelon
variable {α : Type*}
variable {n : ℕ}

theorem pivotOfList_lt_pivotOfList {cols : List (Fin n)} (hsorted : cols.SortedLT) {i j : ℕ}
    (hij : i < j) (hj : pivotOfList cols j ≠ ⊤) : pivotOfList cols i < pivotOfList cols j := by
  have hj' : j < cols.length := by
    by_contra h
    simp [pivotOfList, List.getD, h, Nat.le_of_not_gt h] at hj
    exact hj rfl
  have hi : i < cols.length := lt_trans hij hj'
  have hlt : cols[i] < cols[j] :=
    (hsorted.getElem_lt_getElem_iff (hi := hi) (hj := hj')).2 hij
  simp [pivotOfList, List.getD, hi, hj']
  change (↑cols[i] : WithTop (Fin n)) < ↑cols[j]
  exact WithTop.coe_lt_coe.mpr hlt
