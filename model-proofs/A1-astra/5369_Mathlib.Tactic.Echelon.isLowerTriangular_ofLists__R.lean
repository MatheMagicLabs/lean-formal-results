/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     Mathlib.Tactic.Echelon.isLowerTriangular_ofLists
Source:      Mathlib @ a02a63c2, Mathlib/Tactic/Echelon/Reflection.lean, line 71
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

theorem isLowerTriangular_ofLists [Zero α] {m : ℕ} {rows : List (List α)}
    (h : IsLowerTriangularDiagList 0 m rows) : (ofLists m m rows).IsLowerTriangular := by
  have aux :
      ∀ (rs : List (List α)) (k c i j : ℕ),
        IsLowerTriangularDiagList k c rs →
        i < c → k + i < j →
        (rs[i]?.getD [])[j]?.getD 0 = 0 := by
    intro rs
    induction rs with
    | nil =>
        simp
    | cons row rs ih =>
        intro k c i j h hi hij
        cases h
        · omega
        · rename_i c d hd hdrop htail
          cases i with
          | zero =>
              change row[j]?.getD 0 = 0
              have hget :
                  row[j]? = (d :: List.replicate c 0)[j - k]? := by
                rw [← hdrop, List.getElem?_drop]
                congr 1
                omega
              obtain ⟨t, ht⟩ : ∃ t, j - k = t + 1 :=
                ⟨j - k - 1, by omega⟩
              rw [hget, ht]
              by_cases ht' : t < c <;>
                simp [List.getElem?_replicate, ht']
          | succ i =>
              change (rs[i]?.getD [])[j]?.getD 0 = 0
              exact ih (k + 1) c i j htail (by omega) (by omega)
  have eval :
      ∀ (r c : ℕ) (rs : List (List α)) (i : Fin r) (j : Fin c),
        ofListsFun r c rs i j = (rs[i.val]?.getD [])[j.val]?.getD 0 := by
    intro r
    induction r with
    | zero =>
        intro c rs i
        exact Fin.elim0 i
    | succ r ih =>
        intro c rs i j
        refine Fin.cases ?_ (fun i => ?_) i
        · cases rs <;> simp [ofListsFun]
        · cases rs <;> simp [ofListsFun, ih]
  intro i j hij
  change ofListsFun m m rows i j = 0
  rw [eval]
  exact aux rows 0 m i.val j.val h i.isLt (by simpa using hij)
