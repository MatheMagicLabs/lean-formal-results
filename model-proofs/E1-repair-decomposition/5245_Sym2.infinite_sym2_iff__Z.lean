/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     Sym2.infinite_sym2_iff
Source:      Mathlib @ a02a63c2, Mathlib/Data/Sym/Sym2/Card.lean, line 32
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  E1-repair-decomposition, arm Z, verified in round 1 (round 0 = first attempt)
Prover:      gpt-6-astra
Setup:       GPT-6 Astra, which part of Lean feedback makes repair work: after a shared first attempt (E0), V = full error messages, Z = line numbers only, B = only "Lean rejected this proof"
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
    by_contra hα
    letI : Finite α := not_infinite_iff_finite.mp hα
    exact (not_infinite_iff_finite.mpr
      (inferInstance : Finite (Sym2 α))) h
  · intro h
    letI : Infinite α := h
    apply Infinite.of_injective (fun a : α => s(a, a))
    intro a b hab
    have hm := congrArg (fun z : Sym2 α => a ∈ z) hab
    simpa using hm
