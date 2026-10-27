/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     Function.locallyFinsuppWithin.truncate_zero
Source:      Mathlib @ a02a63c2, Mathlib/Topology/LocallyFinsupp.lean, line 840
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  O3LA3-leanstral-agent-feedback, arm rueck, verified in final
Prover:      labs-leanstral-1-5
Setup:       Leanstral 1.5 agent with goal-state feedback (arm rueck)
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
  calc
    (0 : locallyFinsuppWithin U Y).truncate y hy z = min ((0 : locallyFinsuppWithin U Y) z) y := by
      rw [truncate_apply]
    _ = min (0 : Y) y := rfl
    _ = (0 : Y) := min_eq_left hy
    _ = (0 : locallyFinsuppWithin U Y) z := rfl
