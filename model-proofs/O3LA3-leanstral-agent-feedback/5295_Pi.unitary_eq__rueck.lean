/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     Pi.unitary_eq
Source:      Mathlib @ a02a63c2, Mathlib/Algebra/Star/Unitary.lean, line 232
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  O3LA3-leanstral-agent-feedback, arm rueck, verified in final
Prover:      labs-leanstral-1-5
Setup:       Leanstral 1.5 agent with goal-state feedback (arm rueck)
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

lemma unitary_eq : unitary (Π i, R i) = .pi .univ fun i => unitary (R i) := by
  ext p
  simp [mem_unitary_iff, Submonoid.mem_pi]
