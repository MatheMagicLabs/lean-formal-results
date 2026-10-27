/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     CategoryTheory.Functor.currying₄_unitIso_hom_app_app_app_app_app
Source:      Mathlib @ a02a63c2, Mathlib/CategoryTheory/Functor/CurryingFour.lean, line 75
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  A2-astra-effort-high, arm R, verified in round 2 (round 0 = first attempt)
Prover:      gpt-6-astra
Setup:       GPT-6 Astra, reasoning effort high (arms R, N0)
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
  simp [currying₄, Equivalence.unit, Equivalence.trans, prod.associativity,
    prod.associator, prod.inverseAssociator]
