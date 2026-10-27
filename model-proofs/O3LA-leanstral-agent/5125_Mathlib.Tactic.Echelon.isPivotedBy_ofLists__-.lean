/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     Mathlib.Tactic.Echelon.isPivotedBy_ofLists
Source:      Mathlib @ a02a63c2, Mathlib/Tactic/Echelon/Reflection.lean, line 128
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  O3LA-leanstral-agent, arm -, verified in final
Prover:      labs-leanstral-1-5
Setup:       Leanstral 1.5 as a tool-using agent (Mistral Vibe)
Check:       the proof replaced the human proof in the Mathlib file above; Lean reported
             0 errors and no `sorry`; sorry/admit/native_decide/search tactics were rejected.
-/

open Mathlib.Tactic.Matrix
namespace Mathlib.Tactic.Echelon
variable {α : Type*}
variable {n : ℕ}

theorem isPivotedBy_ofLists [Zero α] {m : ℕ} {rows : List (List α)} {cols : List (Fin n)}
    (hsorted : cols.SortedLT) (h : IsPivotedList cols rows) :
    (ofLists m n rows).IsPivotedBy fun i : Fin m ↦ pivotOfList cols i := by
  refine ⟨?_, ?_⟩
  · intro i₁ i₂ hlt j₂ hzero
    have hmono := pivotOfList_mono_of_sortedLT hsorted
    have hle_nat : (i₁ : ℕ) ≤ (i₂ : ℕ) := by exact_mod_cast hlt.le
    have hp_le : pivotOfList cols (i₁ : ℕ) ≤ pivotOfList cols (i₂ : ℕ) := hmono hle_nat
    by_cases h_lt : (j₂ : WithTop (Fin n)) < pivotOfList cols (i₂ : ℕ)
    · rw [ofLists_apply, ofList_apply]
      exact (getD_of_isPivotedList h (i₂ : ℕ)).1 j₂ h_lt
    · have h_le : pivotOfList cols (i₂ : ℕ) ≤ (j₂ : WithTop (Fin n)) := le_of_not_gt h_lt
      have hp₂_ne_top : pivotOfList cols (i₂ : ℕ) ≠ ⊤ := by
        intro hp_top
        have htop_le : (⊤ : WithTop (Fin n)) ≤ (j₂ : WithTop (Fin n)) := by simpa [hp_top] using h_le
        have h_eq := le_antisymm (le_top (a := (j₂ : WithTop (Fin n)))) htop_le
        exact WithTop.coe_ne_top (a := j₂) h_eq
      have hp₁_ne_top : pivotOfList cols (i₁ : ℕ) ≠ ⊤ := by
        intro hp_top
        have htop_le : (⊤ : WithTop (Fin n)) ≤ (j₂ : WithTop (Fin n)) := by
          simpa [hp_top] using le_trans hp_le h_le
        have h_eq := le_antisymm (le_top (a := (j₂ : WithTop (Fin n)))) htop_le
        exact WithTop.coe_ne_top (a := j₂) h_eq
      obtain ⟨c₁, hc₁⟩ := WithTop.ne_top_iff_exists.mp hp₁_ne_top
      have h_lt_pivots : pivotOfList cols (i₁ : ℕ) < pivotOfList cols (i₂ : ℕ) :=
        pivotOfList_lt_pivotOfList hsorted (by exact_mod_cast hlt) hp₂_ne_top
      have h_j₂_le_c₁ : (j₂ : WithTop (Fin n)) ≤ pivotOfList cols (i₁ : ℕ) := by
        by_contra! h_gt
        have h_c₁_lt_j₂ : c₁ < j₂ := by
          have : (c₁ : WithTop (Fin n)) < (j₂ : WithTop (Fin n)) := by simpa [hc₁] using h_gt
          exact_mod_cast this
        have hzero_c₁ := hzero c₁ h_c₁_lt_j₂
        rw [ofLists_apply, ofList_apply] at hzero_c₁
        have h_nonzero : (rows.getD (i₁ : ℕ) []).getD c₁ 0 ≠ 0 :=
          (getD_of_isPivotedList h (i₁ : ℕ)).2 c₁ hc₁.symm
        exact h_nonzero hzero_c₁
      have h_j₂_lt : (j₂ : WithTop (Fin n)) < pivotOfList cols (i₂ : ℕ) := by
        calc
          (j₂ : WithTop (Fin n)) ≤ pivotOfList cols (i₁ : ℕ) := h_j₂_le_c₁
          _ < pivotOfList cols (i₂ : ℕ) := h_lt_pivots
      exact absurd h_j₂_lt h_lt
  · intro i
    have hget := getD_of_isPivotedList h (i : ℕ)
    simpa [ofLists_apply, ofList_apply] using hget
