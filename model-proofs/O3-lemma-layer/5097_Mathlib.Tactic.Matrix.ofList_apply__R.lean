/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     Mathlib.Tactic.Matrix.ofList_apply
Source:      Mathlib @ a02a63c2, Mathlib/Tactic/Matrix/OfLists.lean, line 47
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  O3-lemma-layer, arm R, verified in round 1 (round 0 = first attempt)
Prover:      claude-opus-5-5
Setup:       Opus 5.5 with repair loop: arm R = repair only; arm RS = repair plus the Lean-checked lemma layer
Check:       the proof replaced the human proof in the Mathlib file above; Lean reported
             0 errors and no `sorry`; sorry/admit/native_decide/search tactics were rejected.
-/

open Matrix
namespace Mathlib.Tactic.Matrix
variable {α : Type*}

@[simp]
theorem ofList_apply [Zero α] (n : ℕ) (l : List α) (i : Fin n) : ofList n l i = l.getD i 0 := by
  first
  | rfl
  | (simp only [ofList]; done)
  | (simp [ofList]; done)
  | (unfold ofList; simp; done)
  | (induction n generalizing l with
     | zero => exact i.elim0
     | succ n ih =>
       rcases l with _ | ⟨a, l⟩ <;>
         refine Fin.cases ?_ (fun j => ?_) i <;>
         simp_all [ofList, Fin.cons, vecCons, Fin.cons_zero, Fin.cons_succ])
