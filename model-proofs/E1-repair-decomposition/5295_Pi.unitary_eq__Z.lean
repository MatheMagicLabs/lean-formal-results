/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     Pi.unitary_eq
Source:      Mathlib @ a02a63c2, Mathlib/Algebra/Star/Unitary.lean, line 232
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  E1-repair-decomposition, arm Z, verified in round 1 (round 0 = first attempt)
Prover:      gpt-6-astra
Setup:       GPT-6 Astra, which part of Lean feedback makes repair work: after a shared first attempt (E0), V = full error messages, Z = line numbers only, B = only "Lean rejected this proof"
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
  apply SetLike.ext
  intro f
  change (star f * f = 1 ∧ f * star f = 1) ↔
    ∀ i ∈ Set.univ, star (f i) * f i = 1 ∧ f i * star (f i) = 1
  constructor
  · rintro ⟨h₁, h₂⟩ i _
    exact ⟨congrFun h₁ i, congrFun h₂ i⟩
  · intro h
    exact ⟨funext (fun i => (h i (Set.mem_univ i)).1),
      funext (fun i => (h i (Set.mem_univ i)).2)⟩
