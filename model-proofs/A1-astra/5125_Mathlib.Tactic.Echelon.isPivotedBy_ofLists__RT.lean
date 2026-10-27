/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     Mathlib.Tactic.Echelon.isPivotedBy_ofLists
Source:      Mathlib @ a02a63c2, Mathlib/Tactic/Echelon/Reflection.lean, line 128
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  A1-astra, arm RT, verified in round 0 (round 0 = first attempt)
Prover:      gpt-6-astra
Setup:       GPT-6 Astra (Codex, effort medium): R = proof plus up to 3 repair rounds with Lean errors; RS = R plus lemma layer; RT = R with read-only Mathlib sources to search; N0-N3 = independent attempts
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
  rw [_root_.Matrix.isPivotedBy_iff]
  refine ⟨?_, ?_, ?_⟩
  · intro i j hij
    exact pivotOfList_mono_of_sortedLT hsorted (Fin.le_def.mp hij)
  · intro i hi j hj hij
    exact pivotOfList_lt_pivotOfList hsorted (Fin.lt_def.mp hij) hj
  · intro i
    simpa only [ofLists_apply, ofList_apply] using
      getD_of_isPivotedList h (i : ℕ)
