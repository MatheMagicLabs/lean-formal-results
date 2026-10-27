/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     Mathlib.Tactic.Echelon.isLowerTriangular_ofLists
Source:      Mathlib @ a02a63c2, Mathlib/Tactic/Echelon/Reflection.lean, line 71
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  A1-astra, arm RS, verified in round 1 (round 0 = first attempt)
Prover:      gpt-6-astra
Setup:       GPT-6 Astra (Codex, effort medium): R = proof plus up to 3 repair rounds with Lean errors; RS = R plus lemma layer; RT = R with read-only Mathlib sources to search; N0-N3 = independent attempts
Check:       the proof replaced the human proof in the Mathlib file above; Lean reported
             0 errors and no `sorry`; sorry/admit/native_decide/search tactics were rejected.
-/

open Mathlib.Tactic.Matrix
namespace Mathlib.Tactic.Echelon
variable {α : Type*}

theorem isLowerTriangular_ofLists [Zero α] {m : ℕ} {rows : List (List α)}
    (h : IsLowerTriangularDiagList 0 m rows) : (ofLists m m rows).IsLowerTriangular := by
  intro i j hij
  change (i : ℕ) < (j : ℕ) at hij
  simpa only [ofLists_apply, ofList_apply] using
    (getD_of_isLowerTriangularDiagList h i.isLt).2 (j : ℕ)
      (by simpa only [Nat.zero_add] using hij)
