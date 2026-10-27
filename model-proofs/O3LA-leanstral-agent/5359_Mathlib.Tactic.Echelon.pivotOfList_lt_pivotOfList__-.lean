/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     Mathlib.Tactic.Echelon.pivotOfList_lt_pivotOfList
Source:      Mathlib @ a02a63c2, Mathlib/Tactic/Echelon/Reflection.lean, line 117
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  O3LA-leanstral-agent, arm -, verified in final
Prover:      labs-leanstral-1-5
Setup:       Leanstral 1.5 as a tool-using agent (Mistral Vibe)
Check:       the proof replaced the human proof in the Mathlib file above; Lean reported
             0 errors and no `sorry`; sorry/admit/native_decide/search tactics were rejected.
-/

open Mathlib.Tactic.Matrix
namespace Mathlib.Tactic.Echelon
variable {α : Type*}
variable {n : ℕ}

theorem pivotOfList_lt_pivotOfList {cols : List (Fin n)} (hsorted : cols.SortedLT) {i j : ℕ}
    (hij : i < j) (hj : pivotOfList cols j ≠ ⊤) : pivotOfList cols i < pivotOfList cols j := by
  have hj_bound : j < cols.length := by
    by_contra! h
    apply hj
    rw [pivotOfList]
    exact List.getElem?_eq_none h
  have hi_bound : i < cols.length := Nat.lt_of_lt_of_le hij (Nat.le_of_lt hj_bound)
  have hlt : cols[i] < cols[j] := hsorted.strictMono_get (by exact hij)
  rw [pivotOfList, pivotOfList, List.getElem?_eq_getElem hi_bound, List.getElem?_eq_getElem hj_bound]
  exact WithTop.coe_lt_coe.mpr hlt
