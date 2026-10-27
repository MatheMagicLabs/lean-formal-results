/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     Mathlib.Tactic.Matrix.ofLists_mul
Source:      Mathlib @ a02a63c2, Mathlib/Tactic/Matrix/OfLists.lean, line 84
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  A1-astra, arm RS, verified in round 0 (round 0 = first attempt)
Prover:      gpt-6-astra
Setup:       GPT-6 Astra (Codex, effort medium): R = proof plus up to 3 repair rounds with Lean errors; RS = R plus lemma layer; RT = R with read-only Mathlib sources to search; N0-N3 = independent attempts
Check:       the proof replaced the human proof in the Mathlib file above; Lean reported
             0 errors and no `sorry`; sorry/admit/native_decide/search tactics were rejected.
-/

open Matrix
namespace Mathlib.Tactic.Matrix
variable {α : Type*}

theorem ofLists_mul [Mul α] [AddCommMonoid α] {l m n : ℕ} {A B C : List (List α)}
    (h : ListMatrix.mul l m n A B = C) : ofLists l m A * ofLists m n B = ofLists l n C := by
  subst C
  ext i j
  rw [Matrix.mul_apply]
  simp only [ofLists_apply, ofList_apply]
  rw [ListMatrix.getD_mul A B i.isLt j.isLt, ListMatrix.dotProduct_eq]
  simp only [dotProduct, ofList_apply]
  apply Finset.sum_congr rfl
  intro k hk
  rw [ListMatrix.getD_transpose B k.val j.isLt]
