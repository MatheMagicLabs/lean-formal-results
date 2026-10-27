/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     Pi.unitary_eq
Source:      Mathlib @ a02a63c2, Mathlib/Algebra/Star/Unitary.lean, line 232
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  O3-lemma-layer, arm R, verified in round 0 (round 0 = first attempt)
Prover:      claude-opus-5-5
Setup:       Opus 5.5 with repair loop: arm R = repair only; arm RS = repair plus the Lean-checked lemma layer
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
  ext x
  simp only [Submonoid.mem_pi, Set.mem_univ, true_implies, forall_const]
  show (star x * x = 1 ∧ x * star x = 1) ↔
    ∀ i, (star (x i) * x i = 1 ∧ x i * star (x i) = 1)
  simp only [funext_iff, Pi.mul_apply, Pi.star_apply, Pi.one_apply, forall_and]
