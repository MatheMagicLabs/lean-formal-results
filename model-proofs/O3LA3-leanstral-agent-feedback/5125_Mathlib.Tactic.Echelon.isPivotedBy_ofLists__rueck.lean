/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     Mathlib.Tactic.Echelon.isPivotedBy_ofLists
Source:      Mathlib @ a02a63c2, Mathlib/Tactic/Echelon/Reflection.lean, line 128
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  O3LA3-leanstral-agent-feedback, arm rueck, verified in final
Prover:      labs-leanstral-1-5
Setup:       Leanstral 1.5 agent with goal-state feedback (arm rueck)
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
    have hmono : Monotone (pivotOfList cols) := pivotOfList_mono_of_sortedLT hsorted
    have hple : pivotOfList cols i₁ ≤ pivotOfList cols i₂ := hmono (Nat.le_of_lt hlt)
    by_cases h₂ : pivotOfList cols i₂ = ⊤
    · rw [ofLists_apply, ofList_apply]
      have hget₂ := getD_of_isPivotedList h i₂
      rcases hget₂ with ⟨hzero₂, hnonzero₂⟩
      exact hzero₂ j₂ (by rw [h₂]; exact WithTop.coe_lt_top j₂)
    · have hlt_p : pivotOfList cols i₁ < pivotOfList cols i₂ :=
        pivotOfList_lt_pivotOfList hsorted hlt h₂
      have h₁ : pivotOfList cols i₁ ≠ ⊤ := by
        intro htop
        rw [htop] at hlt_p
        obtain ⟨c, hc⟩ := WithTop.ne_top_iff_exists.mp h₂
        rw [← hc] at hlt_p
        simpa using hlt_p
      obtain ⟨c, hc⟩ := WithTop.ne_top_iff_exists.mp h₁
      have hnonzero_i₁_c : (ofLists m n rows) i₁ c ≠ 0 := by
        rw [ofLists_apply, ofList_apply]
        exact (getD_of_isPivotedList h i₁).2 c hc.symm
      have hc_not_lt_j₂ : ¬ c < j₂ := by
        intro hcj
        apply hnonzero_i₁_c
        exact hzero c hcj
      have h_j₂_le_c : (j₂ : WithTop (Fin n)) ≤ (c : WithTop (Fin n)) := by
        have : j₂ ≤ c := not_lt.mp hc_not_lt_j₂
        exact WithTop.coe_le_coe.mpr this
      have h_j₂_lt : (j₂ : WithTop (Fin n)) < pivotOfList cols i₂ := by
        -- pivotOfList cols i₁ = (c : WithTop (Fin n)) < pivotOfList cols i₂
        -- and (j₂ : WithTop (Fin n)) ≤ (c : WithTop (Fin n))
        -- so (j₂ : WithTop (Fin n)) < pivotOfList cols i₂
        calc
          (j₂ : WithTop (Fin n)) ≤ (c : WithTop (Fin n)) := h_j₂_le_c
          _ = pivotOfList cols i₁ := by rw [hc.symm]
          _ < pivotOfList cols i₂ := hlt_p
      rw [ofLists_apply, ofList_apply]
      exact (getD_of_isPivotedList h i₂).1 j₂ h_j₂_lt
  · intro i
    have hget := getD_of_isPivotedList h i
    rcases hget with ⟨hzero, hnonzero⟩
    constructor
    · intro j hj
      rw [ofLists_apply, ofList_apply]
      exact hzero j hj
    · intro c hc
      rw [ofLists_apply, ofList_apply]
      exact hnonzero c hc
