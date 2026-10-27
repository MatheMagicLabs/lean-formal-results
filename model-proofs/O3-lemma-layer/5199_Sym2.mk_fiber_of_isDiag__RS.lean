/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     Sym2.mk_fiber_of_isDiag
Source:      Mathlib @ a02a63c2, Mathlib/Data/Sym/Sym2.lean, line 549
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  O3-lemma-layer, arm RS, verified in round 0 (round 0 = first attempt)
Prover:      claude-opus-5-5
Setup:       Opus 5.5 with repair loop: arm R = repair only; arm RS = repair plus the Lean-checked lemma layer
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
  obtain ⟨a, rfl⟩ : ∃ a, z = Sym2.diag a :=
    ⟨z.diagElem hz, (Sym2.diag_diagElem hz).symm⟩
  have h1 : (Sym2.diag a).diagElem hz = a :=
    Sym2.diag_injective (Sym2.diag_diagElem hz)
  rw [h1]
  show Sym2.mk.uncurry ⁻¹' {s(a, a)} = {(a, a)}
  rw [Sym2.mk_fiber]
  simp
