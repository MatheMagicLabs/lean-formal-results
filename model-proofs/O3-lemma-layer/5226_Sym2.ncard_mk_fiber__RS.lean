/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     Sym2.ncard_mk_fiber
Source:      Mathlib @ a02a63c2, Mathlib/Data/Sym/Sym2/Card.lean, line 50
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  O3-lemma-layer, arm RS, verified in round 0 (round 0 = first attempt)
Prover:      claude-opus-5-5
Setup:       Opus 5.5 with repair loop: arm R = repair only; arm RS = repair plus the Lean-checked lemma layer
Check:       the proof replaced the human proof in the Mathlib file above; Lean reported
             0 errors and no `sorry`; sorry/admit/native_decide/search tactics were rejected.
-/

namespace Sym2
open scoped Cardinal
variable {α : Type*}

theorem ncard_mk_fiber [DecidableEq α] (z : Sym2 α) :
    (Sym2.mk.uncurry ⁻¹' {z}).ncard = if z.IsDiag then 1 else 2 := by
  split_ifs with h
  · exact ncard_mk_fiber_of_isDiag h
  · exact ncard_mk_fiber_of_not_isDiag h
