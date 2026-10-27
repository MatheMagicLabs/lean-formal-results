/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     Mathlib.Tactic.Matrix.ofLists_transpose
Source:      Mathlib @ a02a63c2, Mathlib/Tactic/Matrix/OfLists.lean, line 78
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  A2-astra-effort-low, arm R, verified in round 3 (round 0 = first attempt)
Prover:      gpt-6-astra
Setup:       GPT-6 Astra, reasoning effort low (arms R, N0)
Check:       the proof replaced the human proof in the Mathlib file above; Lean reported
             0 errors and no `sorry`; sorry/admit/native_decide/search tactics were rejected.
-/

open Matrix
namespace Mathlib.Tactic.Matrix
variable {α : Type*}

@[simp]
theorem ofLists_transpose [Zero α] (m n : ℕ) (rows : List (List α)) :
    ofLists n m (ListMatrix.transpose n rows) = (ofLists m n rows)ᵀ := by
  have pad_len : ∀ (xs : List α) (ys : List (List α)),
      (ListMatrix.consPad xs ys).length = ys.length := by
    intro xs ys
    induction ys generalizing xs with
    | nil => simp [ListMatrix.consPad]
    | cons y ys ih =>
        cases xs <;> simp [ListMatrix.consPad, ih]
  have trans_len : ∀ (xs : List (List α)),
      (ListMatrix.transpose n xs).length = n := by
    intro xs
    induction xs with
    | nil => simp [ListMatrix.transpose]
    | cons x xs ih => simp [ListMatrix.transpose, pad_len, ih]
  have pad_get : ∀ (ys : List (List α)) (xs : List α) (k : ℕ),
      k < ys.length →
      (ListMatrix.consPad xs ys).getD k [] =
        xs.getD k 0 :: ys.getD k [] := by
    intro ys
    induction ys with
    | nil => simp
    | cons y ys ih =>
        intro xs k hk
        cases xs <;> cases k <;>
          simp_all [ListMatrix.consPad, List.getD]
  have trans_get : ∀ (xs : List (List α)) (i j : ℕ),
      i < n →
      ((ListMatrix.transpose n xs).getD i []).getD j 0 =
        (xs.getD j []).getD i 0 := by
    intro xs
    induction xs with
    | nil =>
        intro i j hi
        simp [ListMatrix.transpose, List.getD, hi]
    | cons x xs ih =>
        intro i j hi
        rw [ListMatrix.transpose, pad_get _ _ i (by simpa [trans_len] using hi)]
        cases j <;> simp_all [List.getD]
  have entry : ∀ (p q : ℕ) (xs : List (List α))
      (i : Fin p) (j : Fin q),
      ofListsFun p q xs i j =
        (xs.getD i.val []).getD j.val 0 := by
    intro p
    induction p with
    | zero =>
        intro q xs i
        exact Fin.elim0 i
    | succ p hp =>
        intro q
        induction q with
        | zero =>
            intro xs i j
            exact Fin.elim0 j
        | succ q hq =>
            intro xs i j
            cases xs with
            | nil =>
                refine Fin.cases ?_ (fun i => ?_) i <;>
                  refine Fin.cases ?_ (fun j => ?_) j <;>
                  simp_all [ofListsFun, List.getD]
            | cons x xs =>
                cases x <;>
                  refine Fin.cases ?_ (fun i => ?_) i <;>
                  refine Fin.cases ?_ (fun j => ?_) j <;>
                  simp_all [ofListsFun, List.getD]
  ext i j
  change ofListsFun n m (ListMatrix.transpose n rows) i j =
    ofListsFun m n rows j i
  rw [entry, entry]
  exact trans_get rows i.val j.val i.isLt
