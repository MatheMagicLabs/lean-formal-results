/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     Mathlib.Tactic.Matrix.ListMatrix.dotProduct_eq
Source:      Mathlib @ a02a63c2, Mathlib/Tactic/Matrix/OfLists.lean, line 71
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  A1-astra, arm RS, verified in round 1 (round 0 = first attempt)
Prover:      gpt-6-astra
Setup:       GPT-6 Astra (Codex, effort medium): R = proof plus up to 3 repair rounds with Lean errors; RS = R plus lemma layer; RT = R with read-only Mathlib sources to search; N0-N3 = independent attempts
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
      simp [ListMatrix.dotProduct_zero, _root_.dotProduct]
  | succ n ih =>
      rw [ListMatrix.dotProduct_add_one, ih]
      simp only [_root_.dotProduct]
      rw [Fin.sum_univ_succ]
      simp only [ofList_apply]
      cases l₁ <;> cases l₂ <;> rfl
