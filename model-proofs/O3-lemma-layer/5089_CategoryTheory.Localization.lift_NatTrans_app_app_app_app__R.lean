/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     CategoryTheory.Localization.lift₄NatTrans_app_app_app_app
Source:      Mathlib @ a02a63c2, Mathlib/CategoryTheory/Localization/Quadrifunctor.lean, line 123
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  O3-lemma-layer, arm R, verified in round 2 (round 0 = first attempt)
Prover:      claude-opus-5-5
Setup:       Opus 5.5 with repair loop: arm R = repair only; arm RS = repair plus the Lean-checked lemma layer
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
  dsimp [lift₄NatTrans, fullyFaithfulUncurry₄, Equivalence.fullyFaithfulFunctor]
  first
  | (simp
     exact liftNatTrans_app _ _ _ _ (uncurry₄.obj F₁') (uncurry₄.obj F₂') (uncurry₄.map τ)
       ⟨X₁, X₂, X₃, X₄⟩)
  | exact liftNatTrans_app _ _ _ _ (uncurry₄.obj F₁') (uncurry₄.obj F₂') (uncurry₄.map τ)
       ⟨X₁, X₂, X₃, X₄⟩
  | (simp
     erw [liftNatTrans_app _ _ _ _ (uncurry₄.obj F₁') (uncurry₄.obj F₂') (uncurry₄.map τ)
       ⟨X₁, X₂, X₃, X₄⟩]
     simp [Lifting.iso])
