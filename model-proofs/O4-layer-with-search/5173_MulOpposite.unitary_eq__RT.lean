/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     MulOpposite.unitary_eq
Source:      Mathlib @ a02a63c2, Mathlib/Algebra/Star/Unitary.lean, line 250
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  O4-layer-with-search, arm RT, verified in round 0 (round 0 = first attempt)
Prover:      claude-opus-5-5
Setup:       Opus 5.5 with repair loop, lemma layer and name search (arm RT)
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
  simp only [Submonoid.mem_op, Unitary.mem_iff]
  constructor <;> rintro ⟨h1, h2⟩ <;> refine ⟨?_, ?_⟩ <;>
    first
    | simpa using congrArg MulOpposite.unop h2
    | simpa using congrArg MulOpposite.unop h1
    | (apply MulOpposite.unop_injective; simpa using h2)
    | (apply MulOpposite.unop_injective; simpa using h1)
