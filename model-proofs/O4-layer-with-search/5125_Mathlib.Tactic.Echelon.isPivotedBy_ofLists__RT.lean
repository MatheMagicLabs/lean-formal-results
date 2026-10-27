/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     Mathlib.Tactic.Echelon.isPivotedBy_ofLists
Source:      Mathlib @ a02a63c2, Mathlib/Tactic/Echelon/Reflection.lean, line 128
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  O4-layer-with-search, arm RT, verified in round 0 (round 0 = first attempt)
Prover:      claude-opus-5-5
Setup:       Opus 5.5 with repair loop, lemma layer and name search (arm RT)
Check:       the proof replaced the human proof in the Mathlib file above; Lean reported
             0 errors and no `sorry`; sorry/admit/native_decide/search tactics were rejected.
-/

open Mathlib.Tactic.Matrix
namespace Mathlib.Tactic.Echelon
variable {α : Type*}
variable {n : ℕ}

theorem isPivotedBy_ofLists [Zero α] {m : ℕ} {rows : List (List α)} {cols : List (Fin n)}
    (hsorted : cols.SortedLT) (h : IsPivotedList cols rows) :
    (ofLists m n rows).IsPivotedBy fun i : Fin m ↦ pivotOfList cols i := by
  rw [Matrix.isPivotedBy_iff]
  refine ⟨?_, ?_, ?_⟩
  · intro i j hij
    exact pivotOfList_mono_of_sortedLT hsorted hij
  · intro i _ j hj hij
    exact pivotOfList_lt_pivotOfList hsorted hij hj
  · intro i
    obtain ⟨h1, h2⟩ := getD_of_isPivotedList h (i : ℕ)
    refine ⟨fun j hj => ?_, fun c hc => ?_⟩
    · rw [ofLists_apply, ofList_apply]
      exact h1 j hj
    · rw [ofLists_apply, ofList_apply]
      exact h2 c hc
