/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     Mathlib.Tactic.Matrix.ListMatrix.dotProduct_eq
Source:      Mathlib @ a02a63c2, Mathlib/Tactic/Matrix/OfLists.lean, line 71
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  O3-lemma-layer, arm RS, verified in round 2 (round 0 = first attempt)
Prover:      claude-opus-5-5
Setup:       Opus 5.5 with repair loop: arm R = repair only; arm RS = repair plus the Lean-checked lemma layer
Check:       the proof replaced the human proof in the Mathlib file above; Lean reported
             0 errors and no `sorry`; sorry/admit/native_decide/search tactics were rejected.
-/

open Matrix
namespace Mathlib.Tactic.Matrix
variable {α : Type*}

@[simp]
theorem ListMatrix.dotProduct_eq [Mul α] [AddCommMonoid α] (n : ℕ) (l₁ l₂ : List α) :
    ListMatrix.dotProduct n l₁ l₂ = ofList n l₁ ⬝ᵥ ofList n l₂ := by
  induction n generalizing l₁ l₂ with
  | zero =>
    rw [ListMatrix.dotProduct_zero]
    first
      | exact (dotProduct_of_isEmpty _ _).symm
      | simp [empty_dotProduct]
      | simp
  | succ n ih =>
    have h : ∀ l : List α, ofList (n+1) l = vecCons (l.headD 0) (ofList n l.tail) := by
      intro l
      funext i
      induction i using Fin.cases with
      | zero => cases l <;> simp [ofList_apply]
      | succ j => cases l <;> simp [ofList_apply, Fin.val_succ, List.getD_cons_succ]
    rw [ListMatrix.dotProduct_add_one, ih, h l₁, h l₂, cons_dotProduct_cons]
