/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     Mathlib.Tactic.Echelon.isLowerTriangular_ofLists
Source:      Mathlib @ a02a63c2, Mathlib/Tactic/Echelon/Reflection.lean, line 71
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  LS1-leanstral-loop, arm L3, verified in round 0 (round 0 = first attempt)
Prover:      labs-leanstral-1-5
Setup:       Leanstral 1.5 in a fixed check-and-repair loop: L1 = 1 candidate per round, L3 = up to 3
Check:       the proof replaced the human proof in the Mathlib file above; Lean reported
             0 errors and no `sorry`; sorry/admit/native_decide/search tactics were rejected.
-/

open Mathlib.Tactic.Matrix
namespace Mathlib.Tactic.Echelon
variable {α : Type*}

theorem isLowerTriangular_ofLists [Zero α] {m : ℕ} {rows : List (List α)}
    (h : IsLowerTriangularDiagList 0 m rows) : (ofLists m m rows).IsLowerTriangular := by
  intro i j hij
  have hi : i.val < m := i.2
  rcases getD_of_isLowerTriangularDiagList h hi with ⟨_, hzero⟩
  have h := hzero j.val (by simpa [zero_add] using hij)
  simpa [ofLists_apply, ofList_apply] using h
