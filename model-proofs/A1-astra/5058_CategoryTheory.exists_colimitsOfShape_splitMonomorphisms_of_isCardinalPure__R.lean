/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     CategoryTheory.exists_colimitsOfShape_splitMonomorphisms_of_isCardinalPure
Source:      Mathlib @ a02a63c2, Mathlib/CategoryTheory/Presentable/CardinalPure.lean, line 147
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  A1-astra, arm R, verified in round 3 (round 0 = first attempt)
Prover:      gpt-6-astra
Setup:       GPT-6 Astra (Codex, effort medium): R = proof plus up to 3 repair rounds with Lean errors; RS = R plus lemma layer; RT = R with read-only Mathlib sources to search; N0-N3 = independent attempts
Check:       the proof replaced the human proof in the Mathlib file above; Lean reported
             0 errors and no `sorry`; sorry/admit/native_decide/search tactics were rejected.
-/

universe w
namespace CategoryTheory
open Limits
variable {C D : Type*} [Category* C] [Category* D] (F : C ⥤ D)
variable (κ : Cardinal.{w}) [Fact κ.IsRegular]
variable (C) in
variable (C) in
attribute [local instance] IsFiltered.isConnected in

lemma exists_colimitsOfShape_splitMonomorphisms_of_isCardinalPure
    [IsCardinalAccessibleCategory C κ] [HasPushouts C] {X Y : C} (f : X ⟶ Y) [IsCardinalPure κ f] :
    ∃ (J : Type w) (_ : SmallCategory J) (_ : IsCardinalFiltered J κ),
      (MorphismProperty.splitMonomorphisms C).colimitsOfShape J f := by
  obtain ⟨J, _, _, ⟨p⟩⟩ :=
    (isCardinalFilteredGenerator_isCardinalPresentable _ κ).exists_colimitsOfShape (Arrow.mk f)
  have := isFiltered_of_isCardinalFiltered J κ
  have := (Arrow.leftFunc (C := C)).preservesColimitsOfShape_of_isCardinalAccessible κ J
  have := (Arrow.rightFunc (C := C)).preservesColimitsOfShape_of_isCardinalAccessible κ J
  have := p.prop_diag_obj
  have sq (j : J) : CommSq (p.diag.obj j).hom (p.ι.app j).left (p.ι.app j).right f := {}
  choose l hl using dsimp% fun j ↦ IsCardinalPure.exists_of_commSq κ (sq j)
  let t : p.diag ⋙ Arrow.leftFunc ⟶ p.diag ⋙ Arrow.rightFunc :=
    Functor.whiskerLeft _ Arrow.leftToRight
  let u : p.diag ⋙ Arrow.leftFunc ⟶ (Functor.const _).obj X :=
    { app j := (p.ι.app j).left
      naturality _ _ g := by
        dsimp
        simpa only [Category.comp_id] using! congr(Arrow.Hom.left $(p.w g)) }
  let v : p.diag ⋙ Arrow.rightFunc ⟶ (Functor.const _).obj Y :=
    { app j := (p.ι.app j).right
      naturality _ _ g := by
        dsimp
        simpa only [Category.comp_id] using! congr(Arrow.Hom.right $(p.w g)) }
  let c₄ : Cocone (pushout t u) :=
    { pt := Y
      ι := pushout.desc v ((Functor.const _).map f) }
  refine ⟨J, inferInstance, inferInstance,
    .mk' _ _ _ c₄ (isColimitConstCocone J X) ?_ (pushout.inr t u)
      (fun j ↦ ?_) f (by cat_disch)⟩
  · exact (IsPushout.of_hasPushout t u).isColimitOfIsColimitOfIsPushout _ _ _ c₄
      (isColimitOfPreserves Arrow.leftFunc p.isColimit)
      (isColimitOfPreserves Arrow.rightFunc p.isColimit)
      (isColimitConstCocone J X)
      (IsPushout.of_id_snd (f := f))
  · exact ⟨⟨{ retraction :=
      ((IsPushout.of_hasPushout t u).app j).desc (l j) (𝟙 _) (by cat_disch) }⟩⟩
