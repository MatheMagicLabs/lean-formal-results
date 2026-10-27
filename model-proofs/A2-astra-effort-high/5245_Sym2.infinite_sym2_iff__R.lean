/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     Sym2.infinite_sym2_iff
Source:      Mathlib @ a02a63c2, Mathlib/Data/Sym/Sym2/Card.lean, line 32
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

@[simp]
theorem infinite_sym2_iff : Infinite (Sym2 α) ↔ Infinite α := by
  classical
  constructor
  · intro h
    letI := h
    by_contra hα
    letI : Finite α := not_infinite_iff_finite.mp hα
    exact not_finite (Sym2 α)
  · intro h
    letI := h
    exact Infinite.of_injective (fun a : α => s(a, a)) (by
      intro a b hab
      simpa using hab)
