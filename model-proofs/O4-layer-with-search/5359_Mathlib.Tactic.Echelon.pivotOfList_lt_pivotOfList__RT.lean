/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     Mathlib.Tactic.Echelon.pivotOfList_lt_pivotOfList
Source:      Mathlib @ a02a63c2, Mathlib/Tactic/Echelon/Reflection.lean, line 117
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  O4-layer-with-search, arm RT, verified in round 1 (round 0 = first attempt)
Prover:      claude-opus-5-5
Setup:       Opus 5.5 with repair loop, lemma layer and name search (arm RT)
Check:       the proof replaced the human proof in the Mathlib file above; Lean reported
             0 errors and no `sorry`; sorry/admit/native_decide/search tactics were rejected.
-/

open Mathlib.Tactic.Matrix
namespace Mathlib.Tactic.Echelon
variable {α : Type*}
variable {n : ℕ}

theorem pivotOfList_lt_pivotOfList {cols : List (Fin n)} (hsorted : cols.SortedLT) {i j : ℕ}
    (hij : i < j) (hj : pivotOfList cols j ≠ ⊤) : pivotOfList cols i < pivotOfList cols j := by
  have hjl : j < cols.length := by
    by_contra h
    push_neg at h
    apply hj
    have hi' : cols.length ≤ j := h
    simp [pivotOfList, List.getElem?_eq_none hi', List.getD_eq_getElem?_getD]
    rfl
  have hil : i < cols.length := by omega
  have key : ∀ k (hk : k < cols.length),
      pivotOfList cols k = ((cols[k] : Fin n) : WithTop (Fin n)) := by
    intro k hk
    simp [pivotOfList, List.getElem?_eq_getElem hk, List.getD_eq_getElem?_getD]
    rfl
  rw [key i hil, key j hjl]
  exact WithTop.coe_lt_coe.mpr ((hsorted.getElem_lt_getElem_iff).mpr hij)
