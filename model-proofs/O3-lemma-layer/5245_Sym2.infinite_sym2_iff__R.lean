/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     Sym2.infinite_sym2_iff
Source:      Mathlib @ a02a63c2, Mathlib/Data/Sym/Sym2/Card.lean, line 32
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  O3-lemma-layer, arm R, verified in round 2 (round 0 = first attempt)
Prover:      claude-opus-5-5
Setup:       Opus 5.5 with repair loop: arm R = repair only; arm RS = repair plus the Lean-checked lemma layer
Check:       the proof replaced the human proof in the Mathlib file above; Lean reported
             0 errors and no `sorry`; sorry/admit/native_decide/search tactics were rejected.
-/

namespace Sym2
open scoped Cardinal
variable {α : Type*}

@[simp]
theorem infinite_sym2_iff : Infinite (Sym2 α) ↔ Infinite α := by
  constructor
  · intro h
    by_contra h'
    rw [not_infinite_iff_finite] at h'
    have hs : Function.Surjective (fun p : α × α => s(p.1, p.2)) := by
      intro z
      revert z
      first
        | refine Sym2.ind ?_
          intro a b
          exact ⟨(a, b), rfl⟩
        | refine Quot.ind ?_
          intro p
          exact ⟨p, rfl⟩
    have : Finite (Sym2 α) := Finite.of_surjective _ hs
    exact not_finite (Sym2 α)
  · intro h
    exact Infinite.of_injective Sym2.diag Sym2.diag_injective
