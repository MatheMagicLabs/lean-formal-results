/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     AlgebraicGeometry.AlgebraicCycle.degree_eq_map_of_unique
Source:      Mathlib @ a02a63c2, Mathlib/AlgebraicGeometry/AlgebraicCycle/Basic.lean, line 119
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  O3LA2-leanstral-agent-variants, arm neu, verified in final
Prover:      labs-leanstral-1-5
Setup:       Leanstral 1.5 agent on the 29 theorems O3LA left open: neu = fresh restart, fest = fixed instruction, staffel = staged budget
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
  have h_default : ∀ x : X, f.base x = default := fun x => Subsingleton.elim _ _
  have h_preimage : f ⁻¹' {default} = Set.univ := by
    ext x; simp [h_default x]
  rw [degree_apply]
  dsimp [AlgebraicCycle.map]
  rw [h_preimage, finsum_mem_univ]
  refine finsum_congr fun x => ?_
  rw [nsmul_eq_mul]
  dsimp [mapCoeff]
  by_cases h_eq : wx x = wy (f.base x)
  · simp [h_eq, mul_comm, Nat.cast_comm]
  · simp [h_eq]
    by_cases hD : D x = 0
    · simp [hD]
    · by_cases h_res : f.residueDegree x = 0
      · simp [h_res]
      · exact absurd (hw x hD h_res) h_eq
