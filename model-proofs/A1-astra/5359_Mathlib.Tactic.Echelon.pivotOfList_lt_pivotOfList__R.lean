/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     Mathlib.Tactic.Echelon.pivotOfList_lt_pivotOfList
Source:      Mathlib @ a02a63c2, Mathlib/Tactic/Echelon/Reflection.lean, line 117
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  A1-astra, arm R, verified in round 2 (round 0 = first attempt)
Prover:      gpt-6-astra
Setup:       GPT-6 Astra (Codex, effort medium): R = proof plus up to 3 repair rounds with Lean errors; RS = R plus lemma layer; RT = R with read-only Mathlib sources to search; N0-N3 = independent attempts
Check:       the proof replaced the human proof in the Mathlib file above; Lean reported
             0 errors and no `sorry`; sorry/admit/native_decide/search tactics were rejected.
-/

open Mathlib.Tactic.Matrix
namespace Mathlib.Tactic.Echelon
variable {α : Type*}
variable {n : ℕ}

theorem pivotOfList_lt_pivotOfList {cols : List (Fin n)} (hsorted : cols.SortedLT) {i j : ℕ}
    (hij : i < j) (hj : pivotOfList cols j ≠ ⊤) : pivotOfList cols i < pivotOfList cols j := by
  have hmem : ∀ (l : List (Fin n)) (k : ℕ),
      pivotOfList l k ≠ ⊤ →
        ∃ a ∈ l, pivotOfList l k = (a : WithTop (Fin n)) := by
    intro l
    induction l with
    | nil =>
        intro k hk
        exact (hk (by rfl)).elim
    | cons a l ih =>
        intro k hk
        cases k with
        | zero =>
            exact ⟨a, by simp, by rfl⟩
        | succ k =>
            have hk' : pivotOfList l k ≠ ⊤ := by
              simpa [pivotOfList] using hk
            obtain ⟨b, hb, he⟩ := ih k hk'
            exact ⟨b, List.mem_cons_of_mem a hb, by
              simpa [pivotOfList] using he⟩
  have main : ∀ (l : List (Fin n)),
      List.Pairwise (· < ·) l → ∀ i j : ℕ,
        i < j → pivotOfList l j ≠ ⊤ →
          pivotOfList l i < pivotOfList l j := by
    intro l
    induction l with
    | nil =>
        intro hs i j hij hj
        exact (hj (by rfl)).elim
    | cons a l ih =>
        intro hs i j hij hj
        obtain ⟨ha, hl⟩ := List.pairwise_cons.mp hs
        cases j with
        | zero => omega
        | succ j =>
            have hj' : pivotOfList l j ≠ ⊤ := by
              simpa [pivotOfList] using hj
            cases i with
            | zero =>
                obtain ⟨b, hb, he⟩ := hmem l j hj'
                have hab : (a : WithTop (Fin n)) < (b : WithTop (Fin n)) := by
                  exact_mod_cast ha b hb
                have he' : pivotOfList (a :: l) (j + 1) =
                    (b : WithTop (Fin n)) := by
                  simpa [pivotOfList] using he
                rw [he']
                change (a : WithTop (Fin n)) < (b : WithTop (Fin n))
                exact hab
            | succ i =>
                simpa [pivotOfList] using
                  ih hl i j (Nat.lt_of_succ_lt_succ hij) hj'
  exact main cols hsorted.pairwise i j hij hj
