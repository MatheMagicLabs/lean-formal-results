/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     AlgebraicGeometry.AlgebraicCycle.degree_eq_map_of_unique
Source:      Mathlib @ a02a63c2, Mathlib/AlgebraicGeometry/AlgebraicCycle/Basic.lean, line 119
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  O3LA3-leanstral-agent-feedback, arm rueck, verified in final
Prover:      labs-leanstral-1-5
Setup:       Leanstral 1.5 agent with goal-state feedback (arm rueck)
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
  have h_base : ∀ x, f.base x = default := fun x => Subsingleton.elim _ _
  have h_preimage : f ⁻¹' {default} = (Set.univ : Set X) := by
    ext x; simp [h_base x]
  calc
    degree f D = ∑ᶠ x, f.residueDegree x • D x := degree_apply f D
    _ = ∑ᶠ x, D x * (Nat.cast (R := R) (f.residueDegree x)) := by
      apply finsum_congr
      intro x
      simp [nsmul_eq_mul, Nat.cast_comm]
    _ = ∑ᶠ x, D x * (Nat.cast (R := R) (mapCoeff f wx wy x)) := by
      apply finsum_congr
      intro x
      by_cases hDx : D x = 0
      · simp [hDx]
      · by_cases hdeg : f.residueDegree x = 0
        · have hmapCoeff : mapCoeff f wx wy x = 0 := by
            dsimp [mapCoeff]
            simp [hdeg]
          simp [hDx, hdeg, hmapCoeff]
        · have hwx : wx x = wy (f.base x) := hw x hDx hdeg
          have hmapCoeff : mapCoeff f wx wy x = f.residueDegree x := by
            dsimp [mapCoeff]
            rw [hwx]
            simp
          simp [hmapCoeff]
    _ = ∑ᶠ x ∈ f ⁻¹' {default}, D x * (Nat.cast (R := R) (mapCoeff f wx wy x)) := by
      rw [h_preimage, finsum_mem_univ]
    _ = map f wx wy D default := by
      simp [AlgebraicCycle.map, Function.locallyFinsupp.map_apply]
