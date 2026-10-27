/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     Mathlib.Tactic.Echelon.pivotOfList_mono_of_sortedLT
Source:      Mathlib @ a02a63c2, Mathlib/Tactic/Echelon/Reflection.lean, line 122
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  O3-lemma-layer, arm RS, verified in round 0 (round 0 = first attempt)
Prover:      claude-opus-5-5
Setup:       Opus 5.5 with repair loop: arm R = repair only; arm RS = repair plus the Lean-checked lemma layer
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
  rcases hij.lt_or_eq with h | h
  · by_cases hj : pivotOfList cols j = ⊤
    · rw [hj]
      exact le_top
    · exact (pivotOfList_lt_pivotOfList hsorted h hj).le
  · subst h
    exact le_rfl
