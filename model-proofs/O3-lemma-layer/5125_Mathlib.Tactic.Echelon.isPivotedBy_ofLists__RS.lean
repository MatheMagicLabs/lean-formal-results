/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     Mathlib.Tactic.Echelon.isPivotedBy_ofLists
Source:      Mathlib @ a02a63c2, Mathlib/Tactic/Echelon/Reflection.lean, line 128
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  O3-lemma-layer, arm RS, verified in round 1 (round 0 = first attempt)
Prover:      claude-opus-5-5
Setup:       Opus 5.5 with repair loop: arm R = repair only; arm RS = repair plus the Lean-checked lemma layer
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
  have hp := getD_of_isPivotedList h
  repeat' constructor
  all_goals first
    | exact fun i j hij => pivotOfList_mono_of_sortedLT hsorted (show (i : ℕ) ≤ j from hij)
    | exact fun i j hij hj => pivotOfList_lt_pivotOfList hsorted (show (i : ℕ) < j from hij) hj
    | exact pivotOfList_mono_of_sortedLT hsorted
    | (intro i j hj
       rw [ofLists_apply, ofList_apply]
       exact (hp i).1 j hj)
    | (intro i c hc
       rw [ofLists_apply, ofList_apply]
       exact (hp i).2 c hc)
    | (intro i j hne
       by_contra hlt
       apply hne
       rw [ofLists_apply, ofList_apply]
       exact (hp i).1 j (lt_of_not_ge hlt))
    | (intro i
       try simp only [ofLists_apply, ofList_apply]
       intro i₂ hi j₂ hz
       apply (hp i₂).1 j₂
       have h1 : (j₂ : WithTop (Fin n)) ≤ pivotOfList cols i := by
         by_contra hlt
         push_neg at hlt
         have hne : pivotOfList cols i ≠ ⊤ := ne_top_of_lt hlt
         obtain ⟨c, hc⟩ := WithTop.ne_top_iff_exists.mp hne
         have hcj : c < j₂ := by
           rw [← hc] at hlt
           exact WithTop.coe_lt_coe.mp hlt
         exact (hp i).2 c hc.symm (hz c hcj)
       by_cases htop : pivotOfList cols i₂ = ⊤
       · rw [htop]; exact WithTop.coe_lt_top _
       · exact lt_of_le_of_lt h1
          (pivotOfList_lt_pivotOfList hsorted (show (i : ℕ) < i₂ from hi) htop))
    | (intro i
       simp only [ofLists_apply, ofList_apply]
       exact ⟨(hp i).1, (hp i).2⟩)
