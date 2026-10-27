/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     Sym2.ncard_mk_fiber
Source:      Mathlib @ a02a63c2, Mathlib/Data/Sym/Sym2/Card.lean, line 50
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

theorem ncard_mk_fiber [DecidableEq α] (z : Sym2 α) :
    (Sym2.mk.uncurry ⁻¹' {z}).ncard = if z.IsDiag then 1 else 2 := by
  refine Sym2.ind (fun a b => ?_) z
  have hs : Sym2.mk.uncurry ⁻¹' {s(a, b)} = ({(a, b), (b, a)} : Set (α × α)) := by
    ext ⟨x, y⟩
    simp [Sym2.eq_iff]
  rw [hs]
  by_cases h : a = b
  · subst h
    simp
  · rw [if_neg (by simpa [Sym2.mk_isDiag_iff] using h)]
    exact Set.ncard_pair (by simp [h])
