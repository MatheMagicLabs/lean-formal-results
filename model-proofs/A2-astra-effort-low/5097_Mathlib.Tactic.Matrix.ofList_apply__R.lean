/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     Mathlib.Tactic.Matrix.ofList_apply
Source:      Mathlib @ a02a63c2, Mathlib/Tactic/Matrix/OfLists.lean, line 47
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  A2-astra-effort-low, arm R, verified in round 1 (round 0 = first attempt)
Prover:      gpt-6-astra
Setup:       GPT-6 Astra, reasoning effort low (arms R, N0)
Check:       the proof replaced the human proof in the Mathlib file above; Lean reported
             0 errors and no `sorry`; sorry/admit/native_decide/search tactics were rejected.
-/

open Matrix
namespace Mathlib.Tactic.Matrix
variable {α : Type*}

@[simp]
theorem ofList_apply [Zero α] (n : ℕ) (l : List α) (i : Fin n) : ofList n l i = l.getD i 0 := by
  induction n generalizing l with
  | zero => exact Fin.elim0 i
  | succ n ih =>
    cases l with
    | nil =>
      refine Fin.cases ?_ (fun j => ?_) i <;>
        simp_all [ofList, List.getD]
    | cons a l =>
      refine Fin.cases ?_ (fun j => ?_) i <;>
        simp_all [ofList, List.getD]
