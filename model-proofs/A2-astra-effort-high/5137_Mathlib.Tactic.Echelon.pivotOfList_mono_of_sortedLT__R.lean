/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     Mathlib.Tactic.Echelon.pivotOfList_mono_of_sortedLT
Source:      Mathlib @ a02a63c2, Mathlib/Tactic/Echelon/Reflection.lean, line 122
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

theorem pivotOfList_mono_of_sortedLT {cols : List (Fin n)} (hsorted : cols.SortedLT) :
    Monotone (pivotOfList cols) := by
  have hpair : cols.Pairwise (· < ·) := by
    simpa only [List.sortedLT_iff_pairwise] using hsorted
  have hget := List.pairwise_iff_getElem.mp hpair
  intro i j hij
  simp only [pivotOfList]
  by_cases hj : j < cols.length
  · have hi : i < cols.length := lt_of_le_of_lt hij hj
    rw [List.getElem?_eq_getElem hi, List.getElem?_eq_getElem hj]
    have hle : cols[i] ≤ cols[j] := by
      rcases eq_or_lt_of_le hij with h | h
      · subst j
        exact le_rfl
      · exact le_of_lt (hget i j hi hj h)
    exact WithTop.coe_le_coe.mpr hle
  · have hj' : cols[j]? = none :=
      List.getElem?_eq_none_iff.mpr (Nat.le_of_not_lt hj)
    rw [hj']
    exact le_top
