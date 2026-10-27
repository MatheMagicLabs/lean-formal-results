/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     AlgebraicGeometry.AlgebraicCycle.degree_eq_map_of_unique
Source:      Mathlib @ a02a63c2, Mathlib/AlgebraicGeometry/AlgebraicCycle/Basic.lean, line 119
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  O3-lemma-layer, arm RS, verified in round 2 (round 0 = first attempt)
Prover:      claude-opus-5-5
Setup:       Opus 5.5 with repair loop: arm R = repair only; arm RS = repair plus the Lean-checked lemma layer
Check:       the proof replaced the human proof in the Mathlib file above; Lean reported
             0 errors and no `sorry`; sorry/admit/native_decide/search tactics were rejected.
-/

namespace AlgebraicGeometry
open CategoryTheory
universe u v
variable {X Y : Scheme.{u}} {R : Type*}
namespace AlgebraicCycle
section map
variable (f : X ⟶ Y) [Semiring R] (c : AlgebraicCycle X R) (x : X) (z : Y)
end map
section degree
variable (f : X ⟶ Y) [CompactSpace X]
section AddCommMonoid
variable [AddCommMonoid R]
open Function.locallyFinsuppWithin in
end AddCommMonoid
section pushforward
variable [QuasiCompact f] [Semiring R] {N : Type*} [DecidableEq N] (wx : X → N) (wy : Y → N)

lemma degree_eq_map_of_unique [Unique Y] (D : AlgebraicCycle X R)
    (hw : ∀ x, D x ≠ 0 → f.residueDegree x ≠ 0 → wx x = wy (f.base x)) :
    degree f D = map f wx wy D default := by
  classical
  rw [degree_apply]
  simp only [map, Function.locallyFinsuppWithin.coe_mk]
  simp
  refine finsum_congr fun x => ?_
  rw [finsum_eq_if, if_pos (Subsingleton.elim _ _)]
  by_cases hD : D x = 0
  · simp [hD]
  by_cases hr : f.residueDegree x = 0
  · simp [hr, mapCoeff]
  have h := hw x hD hr
  first
  | (simp only [mapCoeff, h, if_true]; exact Nat.cast_comm _ _)
  | (simp only [mapCoeff, h, if_true, ite_true]; exact (Nat.cast_comm _ _))
  | (simp [mapCoeff, h]; exact Nat.cast_comm _ _)
  | (simp [mapCoeff, h, Nat.cast_comm])
