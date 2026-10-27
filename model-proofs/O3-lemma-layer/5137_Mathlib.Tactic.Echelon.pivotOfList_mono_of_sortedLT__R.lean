/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     Mathlib.Tactic.Echelon.pivotOfList_mono_of_sortedLT
Source:      Mathlib @ a02a63c2, Mathlib/Tactic/Echelon/Reflection.lean, line 122
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  O3-lemma-layer, arm R, verified in round 3 (round 0 = first attempt)
Prover:      claude-opus-5-5
Setup:       Opus 5.5 with repair loop: arm R = repair only; arm RS = repair plus the Lean-checked lemma layer
Check:       the proof replaced the human proof in the Mathlib file above; Lean reported
             0 errors and no `sorry`; sorry/admit/native_decide/search tactics were rejected.
-/

open Mathlib.Tactic.Matrix
namespace Mathlib.Tactic.Echelon
variable {α : Type*}
variable {n : ℕ}

theorem pivotOfList_mono_of_sortedLT {cols : List (Fin n)} (hsorted : cols.SortedLT) :
    Monotone (pivotOfList cols) := by
  intro i j hij
  unfold pivotOfList
  rcases eq_or_lt_of_le hij with h | h
  · subst h
    exact le_of_eq rfl
  · by_cases hj : j < cols.length
    · have hi : i < cols.length := lt_trans h hj
      rw [List.getElem?_eq_getElem hi, List.getElem?_eq_getElem hj]
      have this := hsorted.strictMono_get
        (Fin.mk_lt_mk.mpr h : (⟨i, hi⟩ : Fin cols.length) < ⟨j, hj⟩)
      simp only [List.get_eq_getElem] at this
      first
      | exact WithTop.coe_le_coe.mpr this.le
      | exact WithBot.coe_le_coe.mpr this.le
      | exact Option.some_le_some.mpr this.le
      | simpa using this.le
      | exact_mod_cast this.le
    · have hnone : cols[j]? = none := List.getElem?_eq_none (by omega)
      first
      | exact le_of_le_of_eq le_top hnone.symm
      | (have hnone' : (cols[j]? : WithTop (Fin n)) = ⊤ := hnone
         exact le_of_le_of_eq le_top hnone'.symm)
      | (rw [hnone]; exact (le_top : _ ≤ (⊤ : WithTop (Fin n))))
