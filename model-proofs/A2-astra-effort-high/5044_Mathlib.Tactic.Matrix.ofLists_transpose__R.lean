/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     Mathlib.Tactic.Matrix.ofLists_transpose
Source:      Mathlib @ a02a63c2, Mathlib/Tactic/Matrix/OfLists.lean, line 78
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  A2-astra-effort-high, arm R, verified in round 3 (round 0 = first attempt)
Prover:      gpt-6-astra
Setup:       GPT-6 Astra, reasoning effort high (arms R, N0)
Check:       the proof replaced the human proof in the Mathlib file above; Lean reported
             0 errors and no `sorry`; sorry/admit/native_decide/search tactics were rejected.
-/

open Matrix
namespace Mathlib.Tactic.Matrix
variable {α : Type*}

@[simp]
theorem ofLists_transpose [Zero α] (m n : ℕ) (rows : List (List α)) :
    ofLists n m (ListMatrix.transpose n rows) = (ofLists m n rows)ᵀ := by
  have hvec : ∀ (n : ℕ) (row : List α) (i : Fin n),
      ofList n row i = row.getD i.val 0 := by
    intro n
    induction n with
    | zero =>
        intro row i
        exact Fin.elim0 i
    | succ n ih =>
        intro row i
        cases row <;> cases i using Fin.cases <;>
          simp [ofList, List.getD, ih]

  have hmat : ∀ (m n : ℕ) (rows : List (List α))
      (i : Fin m) (j : Fin n),
      ofListsFun m n rows i j =
        (rows.getD i.val []).getD j.val 0 := by
    intro m
    induction m with
    | zero =>
        intro n rows i j
        exact Fin.elim0 i
    | succ m ih =>
        intro n rows i j
        cases rows <;> cases i using Fin.cases <;>
          simp [ofListsFun, hvec, ih, List.getD]

  have hpadlen : ∀ (cols : List (List α)) (row : List α),
      cols.length ≤ (ListMatrix.consPad row cols).length := by
    intro cols
    induction cols with
    | nil =>
        intro row
        exact Nat.zero_le _
    | cons col cols ih =>
        intro row
        cases row <;> simp_all [ListMatrix.consPad]

  have hlen : ∀ (rows : List (List α)) (n : ℕ),
      n ≤ (ListMatrix.transpose n rows).length := by
    intro rows
    induction rows with
    | nil =>
        intro n
        simp [ListMatrix.transpose]
    | cons row rows ih =>
        intro n
        exact le_trans (ih n)
          (hpadlen (ListMatrix.transpose n rows) row)

  have hpad : ∀ (cols : List (List α)) (row : List α) (i : ℕ),
      i < cols.length →
      (ListMatrix.consPad row cols).getD i [] =
        row.getD i 0 :: cols.getD i [] := by
    intro cols
    induction cols with
    | nil =>
        intro row i hi
        simp at hi
    | cons col cols ih =>
        intro row i hi
        cases row <;> cases i <;>
          simp_all [ListMatrix.consPad, List.getD]

  have ht : ∀ (rows : List (List α)) (n i j : ℕ),
      i < n →
      ((ListMatrix.transpose n rows).getD i []).getD j 0 =
        (rows.getD j []).getD i 0 := by
    intro rows
    induction rows with
    | nil =>
        intro n i j hi
        simp [ListMatrix.transpose, List.getD, hi]
    | cons row rows ih =>
        intro n i j hi
        rw [ListMatrix.transpose,
          hpad _ _ _ (lt_of_lt_of_le hi (hlen rows n))]
        cases j with
        | zero => rfl
        | succ j =>
            change ((ListMatrix.transpose n rows).getD i []).getD j 0 =
              (rows.getD j []).getD i 0
            exact ih n i j hi

  ext i j
  change ofListsFun n m (ListMatrix.transpose n rows) i j =
    ofListsFun m n rows j i
  rw [hmat, hmat]
  exact ht rows n i.val j.val i.isLt
