/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     Mathlib.Tactic.Echelon.isPivotedBy_ofLists
Source:      Mathlib @ a02a63c2, Mathlib/Tactic/Echelon/Reflection.lean, line 128
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  A1-astra, arm RS, verified in round 3 (round 0 = first attempt)
Prover:      gpt-6-astra
Setup:       GPT-6 Astra (Codex, effort medium): R = proof plus up to 3 repair rounds with Lean errors; RS = R plus lemma layer; RT = R with read-only Mathlib sources to search; N0-N3 = independent attempts
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
  have hmono : Monotone (fun i : Fin m ↦ pivotOfList cols i) :=
    fun _ _ hij ↦ pivotOfList_mono_of_sortedLT hsorted hij
  have hstrict : ∀ i j : Fin m, i < j → pivotOfList cols j ≠ ⊤ →
      pivotOfList cols i < pivotOfList cols j :=
    fun _ _ hij hj ↦ pivotOfList_lt_pivotOfList hsorted hij hj
  have hzero : ∀ i : Fin m, ∀ j : Fin n,
      ↑j < pivotOfList cols i → ofLists m n rows i j = 0 := by
    intro i j hij
    simpa only [ofLists_apply, ofList_apply] using
      (getD_of_isPivotedList h i).1 j hij
  have hne : ∀ i : Fin m, ∀ c : Fin n,
      pivotOfList cols i = c → ofLists m n rows i c ≠ 0 := by
    intro i c hic
    simpa only [ofLists_apply, ofList_apply] using
      (getD_of_isPivotedList h i).2 c hic
  constructor
  · intro i j hij c hc
    apply hzero j c
    by_cases hj : pivotOfList cols j = ⊤
    · simp [hj]
    · cases hp : pivotOfList cols i using WithTop.recTopCoe with
      | top =>
          have hm : pivotOfList cols i ≤ pivotOfList cols j :=
            hmono (le_of_lt hij)
          rw [hp] at hm
          exact lt_of_lt_of_le (by simp) hm
      | coe p =>
          have hpc : c ≤ p := by
            by_contra hcp
            exact hne i p hp (hc p (lt_of_not_ge hcp))
          have hlt := hstrict i j hij hj
          rw [hp] at hlt
          exact lt_of_le_of_lt (by exact_mod_cast hpc) hlt
  · intro i
    exact ⟨hzero i, hne i⟩
