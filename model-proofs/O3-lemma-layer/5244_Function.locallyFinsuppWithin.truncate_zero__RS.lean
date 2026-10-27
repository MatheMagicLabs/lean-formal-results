/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     Function.locallyFinsuppWithin.truncate_zero
Source:      Mathlib @ a02a63c2, Mathlib/Topology/LocallyFinsupp.lean, line 840
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  O3-lemma-layer, arm RS, verified in round 0 (round 0 = first attempt)
Prover:      claude-opus-5-5
Setup:       Opus 5.5 with repair loop: arm R = repair only; arm RS = repair plus the Lean-checked lemma layer
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

@[simp] lemma truncate_zero {hy : 0 ≤ y} : (0 : locallyFinsuppWithin U Y).truncate y hy = 0 := by
  ext z
  rw [truncate_apply]
  have h0 : (0 : locallyFinsuppWithin U Y) z = 0 := rfl
  rw [h0]
  exact min_eq_left hy
