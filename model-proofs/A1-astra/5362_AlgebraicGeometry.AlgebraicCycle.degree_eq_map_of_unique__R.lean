/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     AlgebraicGeometry.AlgebraicCycle.degree_eq_map_of_unique
Source:      Mathlib @ a02a63c2, Mathlib/AlgebraicGeometry/AlgebraicCycle/Basic.lean, line 119
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  A1-astra, arm R, verified in round 2 (round 0 = first attempt)
Prover:      gpt-6-astra
Setup:       GPT-6 Astra (Codex, effort medium): R = proof plus up to 3 repair rounds with Lean errors; RS = R plus lemma layer; RT = R with read-only Mathlib sources to search; N0-N3 = independent attempts
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
  have hw' (x : X) :
      D x = 0 ∨ f.residueDegree x = 0 ∨ wx x = wy default := by
    by_cases hD : D x = 0
    · exact Or.inl hD
    by_cases hf : f.residueDegree x = 0
    · exact Or.inr (Or.inl hf)
    exact Or.inr (Or.inr (by simpa only [hy (f.base x)] using hw x hD hf))
  simp [degree, map, hy]
  all_goals
    first
    | apply finsum_congr
      intro x
      rcases hw' x with h | h | h <;> simp_all [mapCoeff, hy]
      all_goals exact (Nat.cast_commute _ _).eq
    | apply Finset.sum_congr rfl
      intro x hx
      rcases hw' x with h | h | h <;> simp_all [mapCoeff, hy]
      all_goals exact (Nat.cast_commute _ _).eq
