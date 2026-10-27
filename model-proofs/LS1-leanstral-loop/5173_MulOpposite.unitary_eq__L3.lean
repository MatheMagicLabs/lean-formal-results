/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     MulOpposite.unitary_eq
Source:      Mathlib @ a02a63c2, Mathlib/Algebra/Star/Unitary.lean, line 250
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  LS1-leanstral-loop, arm L3, verified in round 0 (round 0 = first attempt)
Prover:      labs-leanstral-1-5
Setup:       Leanstral 1.5 in a fixed check-and-repair loop: L1 = 1 candidate per round, L3 = up to 3
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
  ext p; simp [mem_unitary_iff, Submonoid.mem_op]
