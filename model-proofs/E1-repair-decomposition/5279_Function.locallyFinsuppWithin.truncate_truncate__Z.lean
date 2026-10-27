/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     Function.locallyFinsuppWithin.truncate_truncate
Source:      Mathlib @ a02a63c2, Mathlib/Topology/LocallyFinsupp.lean, line 862
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  E1-repair-decomposition, arm Z, verified in round 0 (round 0 = first attempt)
Prover:      gpt-6-astra
Setup:       GPT-6 Astra, which part of Lean feedback makes repair work: after a shared first attempt (E0), V = full error messages, Z = line numbers only, B = only "Lean rejected this proof"
Check:       the proof replaced the human proof in the Mathlib file above; Lean reported
             0 errors and no `sorry`; sorry/admit/native_decide/search tactics were rejected.
-/

open Filter Function Set
open scoped Topology
variable
variable (U Y) in
variable (X Y) in
namespace Function.locallyFinsuppWithin
variable (U) in
variable (U) in
variable (Y) in
section Lattice
variable [Lattice Y]
variable [AddCommGroup Y]
end Lattice
section LinearOrder
variable [AddCommGroup Y] [LinearOrder Y] [IsOrderedAddMonoid Y]
end LinearOrder
open scoped Classical in
section MapRange
variable {Y Z : Type*} [Zero Y] [Zero Z]
end MapRange
section Truncation
variable {Y : Type*} {y : Y} [Zero Y] [LinearOrder Y]

@[simp] lemma truncate_truncate (D : locallyFinsuppWithin U Y) (y₁ y₂ : Y) (hy₁ : 0 ≤ y₁)
    (hy₂ : 0 ≤ y₂) :
    (D.truncate y₁ hy₁).truncate y₂ hy₂ = D.truncate (min y₁ y₂) (le_min hy₁ hy₂) := by
  ext x
  simp [truncate, min_assoc]
