/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     Sym2.finite_mk_fiber
Source:      Mathlib @ a02a63c2, Mathlib/Data/Sym/Sym2/Card.lean, line 37
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  A2-astra-effort-high, arm R, verified in round 1 (round 0 = first attempt)
Prover:      gpt-6-astra
Setup:       GPT-6 Astra, reasoning effort high (arms R, N0)
Check:       the proof replaced the human proof in the Mathlib file above; Lean reported
             0 errors and no `sorry`; sorry/admit/native_decide/search tactics were rejected.
-/

namespace Sym2
open scoped Cardinal
variable {α : Type*}

theorem finite_mk_fiber (z : Sym2 α) : (Sym2.mk.uncurry ⁻¹' {z}).Finite := by
  classical
  refine Sym2.inductionOn z ?_
  intro a b
  refine ((Set.finite_singleton (a, b)).union
    (Set.finite_singleton (b, a))).subset ?_
  rintro ⟨c, d⟩ h
  change Sym2.mk c d = Sym2.mk a b at h
  simpa [Sym2.eq_iff, or_comm] using h
