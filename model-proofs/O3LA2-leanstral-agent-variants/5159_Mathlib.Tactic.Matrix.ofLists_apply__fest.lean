/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     Mathlib.Tactic.Matrix.ofLists_apply
Source:      Mathlib @ a02a63c2, Mathlib/Tactic/Matrix/OfLists.lean, line 64
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  O3LA2-leanstral-agent-variants, arm fest, verified in final
Prover:      labs-leanstral-1-5
Setup:       Leanstral 1.5 agent on the 29 theorems O3LA left open: neu = fresh restart, fest = fixed instruction, staffel = staged budget
Check:       the proof replaced the human proof in the Mathlib file above; Lean reported
             0 errors and no `sorry`; sorry/admit/native_decide/search tactics were rejected.
-/

open Matrix
namespace Mathlib.Tactic.Matrix
variable {α : Type*}

@[simp]
theorem ofLists_apply [Zero α] (m n : ℕ) (rows : List (List α)) (i : Fin m) :
    ofLists m n rows i = ofList n (rows.getD i []) := by
  ext j
  dsimp [ofLists]
  rw [ofList_apply]
  induction m generalizing rows with
  | zero => exact i.elim0
  | succ m ih =>
    cases rows with
    | nil =>
      cases i using Fin.cases with
      | zero => simp [ofListsFun]
      | succ i' =>
        simp [ofListsFun]
        rw [ih [] i']
        simp
    | cons row rows' =>
      cases i using Fin.cases with
      | zero => simp [ofListsFun]
      | succ i' =>
        simp [ofListsFun]
        rw [ih rows' i']
        simp
