/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     AlgebraicGeometry.AlgebraicCycle.degree_eq_map_of_unique
Source:      Mathlib @ a02a63c2, Mathlib/AlgebraicGeometry/AlgebraicCycle/Basic.lean, line 119
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  A2-astra-effort-high, arm R, verified in round 2 (round 0 = first attempt)
Prover:      gpt-6-astra
Setup:       GPT-6 Astra, reasoning effort high (arms R, N0)
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
  have hy (y : Y) : y = default := Subsingleton.elim _ _
  simp [degree, map, hy, ← nsmul_eq_mul]
  apply finsum_congr
  intro x
  by_cases hD : D x = 0
  · simp [hD]
  by_cases hf : f.residueDegree x = 0
  · simp [mapCoeff, hf]
  simp [mapCoeff, hw x hD hf, nsmul_eq_mul']
  exact (Nat.cast_commute _ _).eq
