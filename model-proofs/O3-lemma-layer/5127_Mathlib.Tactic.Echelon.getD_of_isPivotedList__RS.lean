/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     Mathlib.Tactic.Echelon.getD_of_isPivotedList
Source:      Mathlib @ a02a63c2, Mathlib/Tactic/Echelon/Reflection.lean, line 99
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  O3-lemma-layer, arm RS, verified in round 3 (round 0 = first attempt)
Prover:      claude-opus-5-5
Setup:       Opus 5.5 with repair loop: arm R = repair only; arm RS = repair plus the Lean-checked lemma layer
Check:       the proof replaced the human proof in the Mathlib file above; Lean reported
             0 errors and no `sorry`; sorry/admit/native_decide/search tactics were rejected.
-/

open Mathlib.Tactic.Matrix
namespace Mathlib.Tactic.Echelon
variable {α : Type*}
variable {n : ℕ}

theorem getD_of_isPivotedList [Zero α] {cols : List (Fin n)} {rows : List (List α)}
    (h : IsPivotedList cols rows) (i : ℕ) :
    (∀ j : Fin n, ↑j < pivotOfList cols i → (rows.getD i []).getD j 0 = 0) ∧
      ∀ c : Fin n, pivotOfList cols i = c → (rows.getD i []).getD c 0 ≠ 0 := by
  induction cols generalizing rows i with
  | nil =>
    refine ⟨fun j _ => ?_, fun c hc => ?_⟩
    · cases h
      rename_i hz
      rw [hz]
      simp only [List.getD_eq_getElem?_getD, List.getElem?_map]
      rcases rows[i]? with _ | r <;> simp [List.getElem?_replicate, j.isLt]
    · first
      | (cases hc)
      | (simp [pivotOfList] at hc; cases hc)
      | (simp [pivotOfList] at hc)
  | cons c cs ih =>
    cases rows with
    | nil =>
      exfalso
      first
      | (cases h)
      | (simp [IsPivotedList] at h)
    | cons r rs =>
      cases i with
      | zero =>
        refine ⟨fun j hj => ?_, fun c' hc => ?_⟩
        · have hj' : j < c := by
            first
            | exact WithTop.coe_lt_coe.mp hj
            | simpa [pivotOfList] using hj
            | exact hj
          have hjc : (j : ℕ) < (c : ℕ) := Fin.lt_def.mp hj'
          cases h
          subst_vars
          simp only [List.getD_cons_zero]
          rw [List.getD_eq_getElem?_getD,
            List.getElem?_append_left (by simpa using hjc)]
          simp [List.getElem?_replicate, hjc]
        · have hc' : c = c' := by
            first
            | exact Option.some.inj hc
            | simpa [pivotOfList] using hc
            | exact WithTop.coe_inj.mp hc
          subst hc'
          first
          | (cases h
             subst_vars
             simp only [List.getD_cons_zero]
             rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by simp)]
             simpa using ‹_ ≠ 0›)
          | (cases h <;> simp_all <;> done)
      | succ i =>
        have h' : IsPivotedList cs rs := by
          first
          | (cases h; assumption)
          | exact h.2.2
        simpa [pivotOfList] using ih h' i
