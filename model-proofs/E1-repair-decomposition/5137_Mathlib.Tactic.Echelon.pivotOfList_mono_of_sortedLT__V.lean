/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     Mathlib.Tactic.Echelon.pivotOfList_mono_of_sortedLT
Source:      Mathlib @ a02a63c2, Mathlib/Tactic/Echelon/Reflection.lean, line 122
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  E1-repair-decomposition, arm V, verified in round 2 (round 0 = first attempt)
Prover:      gpt-6-astra
Setup:       GPT-6 Astra, which part of Lean feedback makes repair work: after a shared first attempt (E0), V = full error messages, Z = line numbers only, B = only "Lean rejected this proof"
Check:       the proof replaced the human proof in the Mathlib file above; Lean reported
             0 errors and no `sorry`; sorry/admit/native_decide/search tactics were rejected.
-/

open Mathlib.Tactic.Matrix
namespace Mathlib.Tactic.Echelon
variable {α : Type*}
variable {n : ℕ}

theorem pivotOfList_mono_of_sortedLT {cols : List (Fin n)} (hsorted : cols.SortedLT) :
    Monotone (pivotOfList cols) := by
  have hpair : List.Pairwise (· < ·) cols := by
    first
    | exact hsorted.pairwise
    | exact hsorted.isChain.pairwise
    | exact List.sortedLT_iff_pairwise.mp hsorted
    | simpa [List.SortedLT] using hsorted
  clear hsorted
  revert hpair
  induction cols with
  | nil =>
      intro _ i j hij
      exact le_rfl
  | cons c cs ih =>
      intro hs
      have hh := List.pairwise_cons.mp hs
      have hm := ih hh.2
      intro i j hij
      cases i with
      | zero =>
          cases j with
          | zero => exact le_rfl
          | succ j =>
              have hhead : ∀ b ∈ cs, c < b := hh.1
              clear ih hm hs hh hij
              revert hhead
              induction cs generalizing j with
              | nil =>
                  intro _
                  exact le_top
              | cons d ds ih =>
                  intro hhead
                  cases j with
                  | zero =>
                      have hcd : c ≤ d :=
                        le_of_lt (hhead d (by simp))
                      exact WithTop.coe_le_coe.mpr hcd
                  | succ j =>
                      have htail : ∀ b ∈ ds, c < b :=
                        fun b hb => hhead b (by simp [hb])
                      simpa [pivotOfList] using ih (j := j) htail
      | succ i =>
          cases j with
          | zero => omega
          | succ j =>
              simpa [pivotOfList] using
                hm (Nat.le_of_succ_le_succ hij)
