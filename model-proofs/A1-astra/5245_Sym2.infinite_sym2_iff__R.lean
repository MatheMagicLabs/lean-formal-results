/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     Sym2.infinite_sym2_iff
Source:      Mathlib @ a02a63c2, Mathlib/Data/Sym/Sym2/Card.lean, line 32
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  A1-astra, arm R, verified in round 1 (round 0 = first attempt)
Prover:      gpt-6-astra
Setup:       GPT-6 Astra (Codex, effort medium): R = proof plus up to 3 repair rounds with Lean errors; RS = R plus lemma layer; RT = R with read-only Mathlib sources to search; N0-N3 = independent attempts
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
    by_contra hn
    haveI : Finite α := not_infinite_iff_finite.mp hn
    have hn' : ¬ Infinite (Sym2 α) :=
      not_infinite_iff_finite.mpr inferInstance
    exact hn' h
  · intro h
    letI := h
    apply Infinite.of_injective (fun a : α => s(a, a))
    intro a b hab
    change s(a, a) = s(b, b) at hab
    have hm : a ∈ s(b, b) := by
      rw [← hab]
      simp
    simpa using hm
