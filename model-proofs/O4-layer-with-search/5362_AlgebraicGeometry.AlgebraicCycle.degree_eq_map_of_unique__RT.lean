/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     AlgebraicGeometry.AlgebraicCycle.degree_eq_map_of_unique
Source:      Mathlib @ a02a63c2, Mathlib/AlgebraicGeometry/AlgebraicCycle/Basic.lean, line 119
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  O4-layer-with-search, arm RT, verified in round 2 (round 0 = first attempt)
Prover:      claude-opus-5-5
Setup:       Opus 5.5 with repair loop, lemma layer and name search (arm RT)
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
  rw [degree_apply]
  simp only [map]
  rw [Function.locallyFinsupp.map_apply]
  rw [show (⇑f) ⁻¹' {(default : Y)} = Set.univ from
    Set.eq_univ_of_forall fun x => by
      simp [Set.mem_preimage, Set.mem_singleton_iff, eq_iff_true_of_subsingleton]]
  rw [finsum_mem_univ]
  refine finsum_congr fun x => ?_
  unfold mapCoeff
  split_ifs with h
  · rw [nsmul_eq_mul, Nat.cast_comm]
  · by_cases h1 : D x = 0
    · simp [h1]
    · by_cases h2 : f.residueDegree x = 0
      · simp [h2]
      · exact absurd (hw x h1 h2) h
