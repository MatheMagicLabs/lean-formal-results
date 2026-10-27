/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     Mathlib.Tactic.Echelon.pivotOfList_mono_of_sortedLT
Source:      Mathlib @ a02a63c2, Mathlib/Tactic/Echelon/Reflection.lean, line 122
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  A2-astra-effort-low, arm R, verified in round 3 (round 0 = first attempt)
Prover:      gpt-6-astra
Setup:       GPT-6 Astra, reasoning effort low (arms R, N0)
Check:       the proof replaced the human proof in the Mathlib file above; Lean reported
             0 errors and no `sorry`; sorry/admit/native_decide/search tactics were rejected.
-/

open Mathlib.Tactic.Matrix
namespace Mathlib.Tactic.Echelon
variable {α : Type*}
variable {n : ℕ}

theorem pivotOfList_mono_of_sortedLT {cols : List (Fin n)} (hsorted : cols.SortedLT) :
    Monotone (pivotOfList cols) := by
  intro i j hij
  have hget := List.pairwise_iff_getElem.mp hsorted.pairwise
  unfold pivotOfList
  by_cases hj : j < cols.length
  · have hi : i < cols.length := lt_of_le_of_lt hij hj
    rw [List.getElem?_eq_getElem hi, List.getElem?_eq_getElem hj]
    change (↑cols[i] : WithTop (Fin n)) ≤ ↑cols[j]
    by_cases h : i = j
    · subst j
      exact le_rfl
    · have hlt : i < j := lt_of_le_of_ne hij h
      exact_mod_cast le_of_lt (hget i j hi hj hlt)
  · rw [List.getElem?_eq_none (Nat.le_of_not_gt hj)]
    change _ ≤ (⊤ : WithTop (Fin n))
    exact le_top
