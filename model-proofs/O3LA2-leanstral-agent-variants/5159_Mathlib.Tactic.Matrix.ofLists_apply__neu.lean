/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     Mathlib.Tactic.Matrix.ofLists_apply
Source:      Mathlib @ a02a63c2, Mathlib/Tactic/Matrix/OfLists.lean, line 64
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  O3LA2-leanstral-agent-variants, arm neu, verified in final
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
  induction m generalizing rows with
  | zero => exact i.elim0
  | succ m ih =>
    cases rows with
    | nil =>
      refine Fin.cases ?_ ?_ i
      · ext j ; simp [ofLists, ofListsFun, Matrix.of_apply]
      · intro k ; ext j
        have h := congrArg (fun f => f j) (ih [] k)
        simpa [ofLists, ofListsFun, Matrix.of_apply, ofList_apply, List.getD_nil] using h
    | cons row rows' =>
      refine Fin.cases ?_ ?_ i
      · ext j ; simp [ofLists, ofListsFun, Matrix.of_apply]
      · intro k ; ext j
        have h := congrArg (fun f => f j) (ih rows' k)
        simpa [ofLists, ofListsFun, Matrix.of_apply, ofList_apply] using h
