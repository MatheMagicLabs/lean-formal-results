/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     CategoryTheory.Localization.lift₄NatTrans_app_app_app_app
Source:      Mathlib @ a02a63c2, Mathlib/CategoryTheory/Localization/Quadrifunctor.lean, line 123
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  A2-astra-effort-high, arm R, verified in round 2 (round 0 = first attempt)
Prover:      gpt-6-astra
Setup:       GPT-6 Astra, reasoning effort high (arms R, N0)
Check:       the proof replaced the human proof in the Mathlib file above; Lean reported
             0 errors and no `sorry`; sorry/admit/native_decide/search tactics were rejected.
-/

namespace CategoryTheory
open CategoryTheory.Functor
variable {C₁ C₂ C₃ C₄ D₁ D₂ D₃ D₄ E : Type*}
namespace MorphismProperty
end MorphismProperty
namespace Localization
section
variable (L₁ : C₁ ⥤ D₁) (L₂ : C₂ ⥤ D₂) (L₃ : C₃ ⥤ D₃) (L₄ : C₄ ⥤ D₄)
variable (W₁ : MorphismProperty C₁) (W₂ : MorphismProperty C₂)
end
section
variable (F : C₁ ⥤ C₂ ⥤ C₃ ⥤ C₄ ⥤ E)
end
section
variable (L₁ : C₁ ⥤ D₁) (L₂ : C₂ ⥤ D₂) (L₃ : C₃ ⥤ D₃) (L₄ : C₄ ⥤ D₄)

@[simp]
theorem lift₄NatTrans_app_app_app_app (X₁ : C₁) (X₂ : C₂) (X₃ : C₃) (X₄ : C₄) :
    ((((lift₄NatTrans L₁ L₂ L₃ L₄ W₁ W₂ W₃ W₄ F₁ F₂ F₁' F₂' τ).app
      (L₁.obj X₁)).app (L₂.obj X₂)).app (L₃.obj X₃)).app (L₄.obj X₄) =
        ((((Lifting₄.iso L₁ L₂ L₃ L₄ W₁ W₂ W₃ W₄ F₁ F₁').hom.app X₁).app X₂).app X₃).app X₄ ≫
          (((τ.app X₁).app X₂).app X₃).app X₄ ≫
          ((((Lifting₄.iso L₁ L₂ L₃ L₄ W₁ W₂ W₃ W₄ F₂ F₂').inv.app X₁).app X₂).app X₃).app X₄ := by
  change
    (uncurry₄.map (lift₄NatTrans L₁ L₂ L₃ L₄ W₁ W₂ W₃ W₄
      F₁ F₂ F₁' F₂' τ)).app
      ((L₁.prod (L₂.prod (L₃.prod L₄))).obj (X₁, X₂, X₃, X₄)) =
    (uncurry₄.map
      (Lifting₄.iso L₁ L₂ L₃ L₄ W₁ W₂ W₃ W₄ F₁ F₁').hom).app
        (X₁, X₂, X₃, X₄) ≫
      (uncurry₄.map τ).app (X₁, X₂, X₃, X₄) ≫
      (uncurry₄.map
        (Lifting₄.iso L₁ L₂ L₃ L₄ W₁ W₂ W₃ W₄ F₂ F₂').inv).app
          (X₁, X₂, X₃, X₄)
  simp only [lift₄NatTrans, fullyFaithfulUncurry₄.map_preimage]
  exact liftNatTrans_app
    (L₁.prod (L₂.prod (L₃.prod L₄)))
    (W₁.prod (W₂.prod (W₃.prod W₄)))
    (uncurry₄.obj F₁) (uncurry₄.obj F₂)
    (uncurry₄.obj F₁') (uncurry₄.obj F₂')
    (uncurry₄.map τ) (X₁, X₂, X₃, X₄)
