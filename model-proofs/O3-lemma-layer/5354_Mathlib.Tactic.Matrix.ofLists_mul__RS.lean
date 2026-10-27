/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     Mathlib.Tactic.Matrix.ofLists_mul
Source:      Mathlib @ a02a63c2, Mathlib/Tactic/Matrix/OfLists.lean, line 84
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  O3-lemma-layer, arm RS, verified in round 0 (round 0 = first attempt)
Prover:      claude-opus-5-5
Setup:       Opus 5.5 with repair loop: arm R = repair only; arm RS = repair plus the Lean-checked lemma layer
Check:       the proof replaced the human proof in the Mathlib file above; Lean reported
             0 errors and no `sorry`; sorry/admit/native_decide/search tactics were rejected.
-/

open Matrix
namespace Mathlib.Tactic.Matrix
variable {α : Type*}

theorem ofLists_mul [Mul α] [AddCommMonoid α] {l m n : ℕ} {A B C : List (List α)}
    (h : ListMatrix.mul l m n A B = C) : ofLists l m A * ofLists m n B = ofLists l n C := by
  subst h
  ext i j
  rw [Matrix.mul_apply, ofLists_apply l n, ofList_apply,
    ListMatrix.getD_mul _ _ i.isLt j.isLt, ListMatrix.dotProduct_eq]
  simp only [_root_.dotProduct, ofLists_apply, ofList_apply]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [ListMatrix.getD_transpose _ _ j.isLt]
