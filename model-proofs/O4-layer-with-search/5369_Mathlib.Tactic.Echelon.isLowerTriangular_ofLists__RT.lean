/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     Mathlib.Tactic.Echelon.isLowerTriangular_ofLists
Source:      Mathlib @ a02a63c2, Mathlib/Tactic/Echelon/Reflection.lean, line 71
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

theorem isLowerTriangular_ofLists [Zero α] {m : ℕ} {rows : List (List α)}
    (h : IsLowerTriangularDiagList 0 m rows) : (ofLists m m rows).IsLowerTriangular := by
  intro i j hij
  rw [ofLists_apply, ofList_apply]
  exact (getD_of_isLowerTriangularDiagList h i.2).2 j
    (by rw [zero_add]; exact Fin.lt_def.mp (OrderDual.toDual_lt_toDual.mp hij))
