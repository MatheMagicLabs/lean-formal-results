/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     Mathlib.Tactic.Matrix.ofLists_transpose
Source:      Mathlib @ a02a63c2, Mathlib/Tactic/Matrix/OfLists.lean, line 78
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  A1-astra, arm R, verified in round 3 (round 0 = first attempt)
Prover:      gpt-6-astra
Setup:       GPT-6 Astra (Codex, effort medium): R = proof plus up to 3 repair rounds with Lean errors; RS = R plus lemma layer; RT = R with read-only Mathlib sources to search; N0-N3 = independent attempts
Check:       the proof replaced the human proof in the Mathlib file above; Lean reported
             0 errors and no `sorry`; sorry/admit/native_decide/search tactics were rejected.
-/

open Matrix
namespace Mathlib.Tactic.Matrix
variable {α : Type*}

@[simp]
theorem ofLists_transpose [Zero α] (m n : ℕ) (rows : List (List α)) :
    ofLists n m (ListMatrix.transpose n rows) = (ofLists m n rows)ᵀ := by
  have hrow : ∀ k (i : Fin k), ofList k ([] : List α) i = 0 := by
    intro k
    induction k with
    | zero => intro i; exact Fin.elim0 i
    | succ k ih =>
        intro i
        refine Fin.cases ?_ (fun i => ?_) i <;>
          simp_all [ofList]

  have hempty : ∀ p q (i : Fin p) (j : Fin q),
      ofListsFun p q ([] : List (List α)) i j = 0 := by
    intro p
    induction p with
    | zero => intro q i j; exact Fin.elim0 i
    | succ p ih =>
        intro q i j
        refine Fin.cases ?_ (fun i => ?_) i <;>
          simp_all [ofListsFun]

  have hrep : ∀ p q (i : Fin p) (j : Fin q),
      ofListsFun p q (List.replicate p ([] : List α)) i j = 0 := by
    intro p
    induction p with
    | zero => intro q i j; exact Fin.elim0 i
    | succ p ih =>
        intro q i j
        refine Fin.cases ?_ (fun i => ?_) i <;>
          simp_all [ofListsFun, List.replicate_succ]

  have hlenPad : ∀ (cols : List (List α)) (row : List α),
      (ListMatrix.consPad row cols).length = cols.length := by
    intro cols
    induction cols with
    | nil =>
        intro row
        cases row <;> simp [ListMatrix.consPad]
    | cons col cols ih =>
        intro row
        cases row <;> simp_all [ListMatrix.consPad]

  have hlen : ∀ (rows : List (List α)) n,
      (ListMatrix.transpose n rows).length = n := by
    intro rows
    induction rows with
    | nil => intro n; simp [ListMatrix.transpose]
    | cons row rows ih =>
        intro n
        simpa [ListMatrix.transpose, hlenPad] using ih n

  have hpad : ∀ p q (row : List α) (cols : List (List α)),
      cols.length = p → ∀ (i : Fin p) (j : Fin (q + 1)),
      ofListsFun p (q + 1) (ListMatrix.consPad row cols) i j =
        Fin.cases (ofList p row i) (fun j => ofListsFun p q cols i j) j := by
    intro p
    induction p with
    | zero =>
        intro q row cols h i j
        exact Fin.elim0 i
    | succ p ih =>
        intro q row cols h i j
        cases cols with
        | nil => simp at h
        | cons col cols =>
            have hc : cols.length = p := by simpa using h
            cases row with
            | nil =>
                refine Fin.cases ?_ (fun i => ?_) i
                · refine Fin.cases ?_ (fun j => ?_) j <;>
                    simp [ListMatrix.consPad, ofListsFun, ofList]
                · simpa [ListMatrix.consPad, ofListsFun, ofList] using
                    ih q [] cols hc i j
            | cons a row =>
                refine Fin.cases ?_ (fun i => ?_) i
                · refine Fin.cases ?_ (fun j => ?_) j <;>
                    simp [ListMatrix.consPad, ofListsFun, ofList]
                · simpa [ListMatrix.consPad, ofListsFun, ofList] using
                    ih q row cols hc i j

  induction rows generalizing m with
  | nil =>
      ext i j
      change ofListsFun n m (ListMatrix.transpose n []) i j =
        ofListsFun m n [] j i
      simp [ListMatrix.transpose, hrep, hempty]
  | cons row rows ih =>
      cases m with
      | zero =>
          ext i j
          exact Fin.elim0 j
      | succ m =>
          ext i j
          change ofListsFun n (m + 1)
              (ListMatrix.transpose n (row :: rows)) i j =
            ofListsFun (m + 1) n (row :: rows) j i
          rw [ListMatrix.transpose, hpad n m row _ (hlen rows n)]
          refine Fin.cases ?_ (fun j => ?_) j
          · simp [ofListsFun]
          · simpa [ofLists, ofListsFun] using
              congrFun (congrFun (ih (m := m)) i) j
