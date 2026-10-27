/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     CategoryTheory.exists_colimitsOfShape_splitMonomorphisms_of_isCardinalPure
Source:      Mathlib @ a02a63c2, Mathlib/CategoryTheory/Presentable/CardinalPure.lean, line 147
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  A1-astra, arm RT, verified in round 1 (round 0 = first attempt)
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
  classical
  obtain ⟨J, _, _, ⟨p⟩⟩ :=
    (isCardinalFilteredGenerator_isCardinalPresentable (Arrow C) κ).exists_colimitsOfShape
      (Arrow.mk f)
  haveI := isFiltered_of_isCardinalFiltered J κ
  haveI : PreservesColimitsOfShape J (Arrow.leftFunc : Arrow C ⥤ C) :=
    Functor.preservesColimitsOfShape_of_isCardinalAccessible Arrow.leftFunc κ J
  haveI : PreservesColimitsOfShape J (Arrow.rightFunc : Arrow C ⥤ C) :=
    Functor.preservesColimitsOfShape_of_isCardinalAccessible Arrow.rightFunc κ J
  haveI (j : J) : IsCardinalPresentable (p.diag.obj j) κ := p.prop_diag_obj j
  let a := p.toColimitPresentation.map Arrow.leftFunc
  let b := p.toColimitPresentation.map Arrow.rightFunc
  let t : a.diag ⟶ b.diag := Functor.whiskerLeft p.diag Arrow.leftToRight
  let u : (Functor.const J).obj X ⟶ (Functor.const J).obj Y :=
    (Functor.const J).map f
  have h : a.ι ≫ u = t ≫ b.ι := by
    ext j
    simpa [a, b, t, u, ColimitPresentation.map] using (p.ι.app j).w
  have hw (j : J) : a.ι.app j ≫ f = t.app j ≫ b.ι.app j := by
    simpa [u] using congrArg (fun α => α.app j) h
  let v := pushout.inl a.ι t
  let r := pushout.inr a.ι t
  let s := pushout.desc u b.ι h
  have hv : v ≫ s = u := by
    simp [v, s]
  have hr : r ≫ s = b.ι := by
    simp [r, s]
  have hvj (j : J) : v.app j ≫ s.app j = f := by
    simpa [u] using congrArg (fun α => α.app j) hv
  have hrj (j : J) : r.app j ≫ s.app j = b.ι.app j := by
    simpa using congrArg (fun α => α.app j) hr
  let c : Cocone (pushout a.ι t) := Cocone.mk Y s
  have hc : IsColimit c := by
    refine (IsPushout.of_hasPushout a.ι t).isColimitOfIsColimitOfIsPushout
      a.cocone (constCocone J X) b.cocone c
      a.isColimit (isColimitConstCocone J X) b.isColimit
      (IsPushout.of_id_fst (f := f)) ?_ ?_ ?_ ?_
    · intro j
      simp
    · intro j
      exact hw j
    · intro j
      simpa [c] using (hvj j).symm
    · intro j
      simpa [c, r] using (hrj j).symm
  refine ⟨J, inferInstance, inferInstance,
    MorphismProperty.colimitsOfShape.mk'
      _ _ (constCocone J X) c (isColimitConstCocone J X) hc v ?_ f ?_⟩
  · intro j
    haveI : IsCardinalPresentable (a.diag.obj j) κ :=
      inferInstanceAs (IsCardinalPresentable (p.diag.obj j).left κ)
    haveI : IsCardinalPresentable (b.diag.obj j) κ :=
      inferInstanceAs (IsCardinalPresentable (p.diag.obj j).right κ)
    obtain ⟨ρ, hρ⟩ := IsCardinalPure.exists_of_commSq κ
      (show CommSq (t.app j) (a.ι.app j) (b.ι.app j) f from ⟨(hw j).symm⟩)
    let sq := (IsPushout.of_hasPushout a.ι t).app j
    exact ⟨⟨{
      retraction := sq.desc (𝟙 X) ρ (by simpa using hρ.symm)
      id := by simp [v, sq]
    }⟩⟩
  · intro j
    simpa [c] using (hvj j).symm
