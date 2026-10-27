/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     CategoryTheory.Functor.currying₄_unitIso_hom_app_app_app_app_app
Source:      Mathlib @ a02a63c2, Mathlib/CategoryTheory/Functor/CurryingFour.lean, line 75
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  O3-lemma-layer, arm R, verified in round 3 (round 0 = first attempt)
Prover:      claude-opus-5-5
Setup:       Opus 5.5 with repair loop: arm R = repair only; arm RS = repair plus the Lean-checked lemma layer
Check:       the proof replaced the human proof in the Mathlib file above; Lean reported
             0 errors and no `sorry`; sorry/admit/native_decide/search tactics were rejected.
-/

namespace CategoryTheory
namespace Functor
variable {C₁ C₂ C₃ C₄ D₁ D₂ D₃ D₄ E : Type*}

@[simp]
lemma currying₄_unitIso_hom_app_app_app_app_app (F : C₁ ⥤ C₂ ⥤ C₃ ⥤ C₄ ⥤ E)
    (X₁ : C₁) (X₂ : C₂) (X₃ : C₃) (X₄ : C₄) :
    ((((currying₄.unitIso.hom.app F).app X₁).app X₂).app X₃).app X₄ = 𝟙 _ := by
  have h1 : (((prod.associativity (C₁ × C₂) C₃ C₄).trans
      (prod.associativity C₁ C₂ (C₃ × C₄))).unit.app (((X₁, X₂), X₃), X₄)).1.1.1 = 𝟙 X₁ := by
    first
    | simp [Equivalence.unit, Equivalence.trans, prod.associativity]
    | (dsimp [Equivalence.unit, Equivalence.trans, prod.associativity]; simp)
    | simp [Equivalence.unit, Equivalence.trans]
    | rfl
  have h2 : (((prod.associativity (C₁ × C₂) C₃ C₄).trans
      (prod.associativity C₁ C₂ (C₃ × C₄))).unit.app (((X₁, X₂), X₃), X₄)).1.1.2 = 𝟙 X₂ := by
    first
    | simp [Equivalence.unit, Equivalence.trans, prod.associativity]
    | (dsimp [Equivalence.unit, Equivalence.trans, prod.associativity]; simp)
    | simp [Equivalence.unit, Equivalence.trans]
    | rfl
  have h3 : (((prod.associativity (C₁ × C₂) C₃ C₄).trans
      (prod.associativity C₁ C₂ (C₃ × C₄))).unit.app (((X₁, X₂), X₃), X₄)).1.2 = 𝟙 X₃ := by
    first
    | simp [Equivalence.unit, Equivalence.trans, prod.associativity]
    | (dsimp [Equivalence.unit, Equivalence.trans, prod.associativity]; simp)
    | simp [Equivalence.unit, Equivalence.trans]
    | rfl
  have h4 : (((prod.associativity (C₁ × C₂) C₃ C₄).trans
      (prod.associativity C₁ C₂ (C₃ × C₄))).unit.app (((X₁, X₂), X₃), X₄)).2 = 𝟙 X₄ := by
    first
    | simp [Equivalence.unit, Equivalence.trans, prod.associativity]
    | (dsimp [Equivalence.unit, Equivalence.trans, prod.associativity]; simp)
    | simp [Equivalence.unit, Equivalence.trans]
    | rfl
  first
  | (simp [currying₄]; rw [h1, h2, h3, h4]; simp)
  | (simp [currying₄, h1, h2, h3, h4])
  | (simp only [currying₄]; simp [h1, h2, h3, h4])
  | (simp [currying₄, Equivalence.unit, Equivalence.trans, prod.associativity])
