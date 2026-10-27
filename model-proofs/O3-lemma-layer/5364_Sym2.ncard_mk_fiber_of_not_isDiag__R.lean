/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     Sym2.ncard_mk_fiber_of_not_isDiag
Source:      Mathlib @ a02a63c2, Mathlib/Data/Sym/Sym2/Card.lean, line 45
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  O3-lemma-layer, arm R, verified in round 0 (round 0 = first attempt)
Prover:      claude-opus-5-5
Setup:       Opus 5.5 with repair loop: arm R = repair only; arm RS = repair plus the Lean-checked lemma layer
Check:       the proof replaced the human proof in the Mathlib file above; Lean reported
             0 errors and no `sorry`; sorry/admit/native_decide/search tactics were rejected.
-/

namespace Sym2
open scoped Cardinal
variable {α : Type*}

theorem ncard_mk_fiber_of_not_isDiag {z : Sym2 α} (hz : ¬z.IsDiag) :
    (Sym2.mk.uncurry ⁻¹' {z}).ncard = 2 := by
  induction z using Sym2.ind with
  | _ a b =>
  have hab : a ≠ b := by simpa using hz
  have h : (Sym2.mk.uncurry ⁻¹' {s(a, b)}) = {(a, b), (b, a)} := by
    ext ⟨x, y⟩
    simp [Function.uncurry, Sym2.eq_iff, Set.mem_preimage, Set.mem_singleton_iff,
      Set.mem_insert_iff, Prod.mk.injEq]
  rw [h]
  exact Set.ncard_pair (by simp [hab])
