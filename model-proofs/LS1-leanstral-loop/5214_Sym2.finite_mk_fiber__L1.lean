/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     Sym2.finite_mk_fiber
Source:      Mathlib @ a02a63c2, Mathlib/Data/Sym/Sym2/Card.lean, line 37
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  LS1-leanstral-loop, arm L1, verified in round 1 (round 0 = first attempt)
Prover:      labs-leanstral-1-5
Setup:       Leanstral 1.5 in a fixed check-and-repair loop: L1 = 1 candidate per round, L3 = up to 3
Check:       the proof replaced the human proof in the Mathlib file above; Lean reported
             0 errors and no `sorry`; sorry/admit/native_decide/search tactics were rejected.
-/

namespace Sym2
open scoped Cardinal
variable {α : Type*}

theorem finite_mk_fiber (z : Sym2 α) : (Sym2.mk.uncurry ⁻¹' {z}).Finite := by
  obtain ⟨⟨a, b⟩, h⟩ := Sym2.mk_surjective z
  rw [← h]
  have h_fiber := Sym2.mk_fiber a b
  have h_finite : Set.Finite ({(a, b), (b, a)} : Set (α × α)) :=
    Set.Finite.insert (a, b) (Set.finite_singleton (b, a))
  exact h_fiber ▸ h_finite
