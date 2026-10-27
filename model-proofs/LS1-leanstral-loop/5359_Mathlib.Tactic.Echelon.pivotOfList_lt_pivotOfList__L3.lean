/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     Mathlib.Tactic.Echelon.pivotOfList_lt_pivotOfList
Source:      Mathlib @ a02a63c2, Mathlib/Tactic/Echelon/Reflection.lean, line 117
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  LS1-leanstral-loop, arm L3, verified in round 3 (round 0 = first attempt)
Prover:      labs-leanstral-1-5
Setup:       Leanstral 1.5 in a fixed check-and-repair loop: L1 = 1 candidate per round, L3 = up to 3
Check:       the proof replaced the human proof in the Mathlib file above; Lean reported
             0 errors and no `sorry`; sorry/admit/native_decide/search tactics were rejected.
-/

open Mathlib.Tactic.Matrix
namespace Mathlib.Tactic.Echelon
variable {α : Type*}
variable {n : ℕ}

theorem pivotOfList_lt_pivotOfList {cols : List (Fin n)} (hsorted : cols.SortedLT) {i j : ℕ}
    (hij : i < j) (hj : pivotOfList cols j ≠ ⊤) : pivotOfList cols i < pivotOfList cols j := by
  have hj_len : j < cols.length := by
    have hsome := Option.ne_none_iff_exists.mp hj
    rcases hsome with ⟨x, hx⟩
    have hx' : cols[j]? = some x := hx.symm
    exact ((List.getElem?_eq_some_iff).mp hx').1
  have hi_len : i < cols.length := lt_trans hij hj_len
  have h_lt_fin : cols[i] < cols[j] :=
    (hsorted.getElem_lt_getElem_iff (hi := hi_len) (hj := hj_len)).mpr hij
  have hpi_some : cols[i]? = some (cols[i]) :=
    ((List.getElem?_eq_some_iff).mpr ⟨hi_len, rfl⟩)
  have hpj_some : cols[j]? = some (cols[j]) :=
    ((List.getElem?_eq_some_iff).mpr ⟨hj_len, rfl⟩)
  dsimp [pivotOfList]
  rw [hpi_some, hpj_some]
  exact WithTop.coe_lt_coe.mpr h_lt_fin
