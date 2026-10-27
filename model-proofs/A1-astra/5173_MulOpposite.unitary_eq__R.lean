/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     MulOpposite.unitary_eq
Source:      Mathlib @ a02a63c2, Mathlib/Algebra/Star/Unitary.lean, line 250
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  A1-astra, arm R, verified in round 0 (round 0 = first attempt)
Prover:      gpt-6-astra
Setup:       GPT-6 Astra (Codex, effort medium): R = proof plus up to 3 repair rounds with Lean errors; RS = R plus lemma layer; RT = R with read-only Mathlib sources to search; N0-N3 = independent attempts
Check:       the proof replaced the human proof in the Mathlib file above; Lean reported
             0 errors and no `sorry`; sorry/admit/native_decide/search tactics were rejected.
-/

variable {R : Type*}
namespace Unitary
section Monoid
variable [Monoid R] [StarMul R]
end Monoid
end Unitary
namespace Prod
variable {R S : Type*} [Monoid R] [Monoid S] [StarMul R] [StarMul S]
variable (R S) in
end Prod
namespace Pi
variable {ι} {R : ι → Type*} [Π i, Monoid (R i)] [Π i, StarMul (R i)]
variable (R) in
end Pi
namespace MulOpposite
variable {R : Type*} [Monoid R] [StarMul R]
variable (R) in

lemma unitary_eq : unitary Rᵐᵒᵖ = (unitary R).op := by
  ext x
  constructor
  · rintro ⟨h₁, h₂⟩
    exact ⟨congrArg unop h₂, congrArg unop h₁⟩
  · rintro ⟨h₁, h₂⟩
    exact ⟨congrArg op h₂, congrArg op h₁⟩
