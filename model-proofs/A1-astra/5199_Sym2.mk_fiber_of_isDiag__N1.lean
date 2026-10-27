/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     Sym2.mk_fiber_of_isDiag
Source:      Mathlib @ a02a63c2, Mathlib/Data/Sym/Sym2.lean, line 549
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  A1-astra, arm N1, verified in round 0 (round 0 = first attempt)
Prover:      gpt-6-astra
Setup:       GPT-6 Astra (Codex, effort medium): R = proof plus up to 3 repair rounds with Lean errors; RS = R plus lemma layer; RT = R with read-only Mathlib sources to search; N0-N3 = independent attempts
Check:       the proof replaced the human proof in the Mathlib file above; Lean reported
             0 errors and no `sorry`; sorry/admit/native_decide/search tactics were rejected.
-/

open List (Vector)
open Finset Function Sym
universe u
variable {α β γ : Type*}
namespace Sym2
attribute [refl] Rel.refl
end Sym2
namespace Sym2
section Membership
variable {x : α}
end Membership
variable {z : Sym2 α} {f : α → β}
variable (z) in

theorem mk_fiber_of_isDiag (hz : z.IsDiag) :
    Sym2.mk.uncurry ⁻¹' {z} = {Function.diag (z.diagElem hz)} := by
  revert hz
  refine Sym2.inductionOn z ?_
  intro a b hz
  have hab : a = b := by simpa using hz
  subst b
  ext ⟨x, y⟩
  simp [Function.uncurry, Function.diag, Sym2.eq_iff]
