/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     Sym2.mk_fiber_of_isDiag
Source:      Mathlib @ a02a63c2, Mathlib/Data/Sym/Sym2.lean, line 549
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  O3-lemma-layer, arm R, verified in round 2 (round 0 = first attempt)
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
  revert hz
  induction z using Sym2.ind with
  | h x y =>
    intro hz
    have hxy : x = y := hz
    subst hxy
    have h : Sym2.diagElem s(x, x) hz = x := by
      first
        | rfl
        | simp [Sym2.diagElem]
        | (unfold Sym2.diagElem; rfl)
    rw [h]
    ext ⟨a, b⟩
    first
      | (simp [Function.diag, Function.uncurry, Set.mem_preimage, Set.mem_singleton_iff,
          Sym2.eq_iff]; done)
      | (simp [Function.diag, Function.uncurry, Set.mem_preimage, Set.mem_singleton_iff]
         aesop)
