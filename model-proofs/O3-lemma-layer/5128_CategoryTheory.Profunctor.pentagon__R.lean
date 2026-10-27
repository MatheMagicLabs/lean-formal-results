/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     CategoryTheory.Profunctor.pentagon
Source:      Mathlib @ a02a63c2, Mathlib/CategoryTheory/Profunctor/Bicategory.lean, line 58
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  O3-lemma-layer, arm R, verified in round 2 (round 0 = first attempt)
Prover:      claude-opus-5-5
Setup:       Opus 5.5 with repair loop: arm R = repair only; arm RS = repair plus the Lean-checked lemma layer
Check:       the proof replaced the human proof in the Mathlib file above; Lean reported
             0 errors and no `sorry`; sorry/admit/native_decide/search tactics were rejected.
-/

universe w v u
namespace CategoryTheory
set_option linter.checkUnivs false in
attribute [instance] ProfCat.str
namespace ProfCat
end ProfCat
open Limits Types Profunctor
namespace Profunctor
section

@[reassoc (attr := simp)]
lemma pentagon {C D E F G : Type u} [Category* C] [Category* D] [Category* E]
  [Category* F] [Category* G] (P : Profunctor.{max u w} C D) (Q : Profunctor.{max u w} D E)
    (R : Profunctor.{max u w} E F) (S : Profunctor.{max u w} F G) :
    whiskerRight S (P.associator Q R).hom ≫
        (P.associator (Q.comp R) S).hom ≫ P.whiskerLeft (Q.associator R S).hom =
      ((P.comp Q).associator R S).hom ≫ (P.associator Q (R.comp S)).hom := by
  ext c g x
  first
    | (obtain ⟨⟨f, y, s⟩⟩ := x
       obtain ⟨⟨e, z, r⟩⟩ := y
       obtain ⟨⟨d, p, q⟩⟩ := z
       first
         | rfl
         | (simp [associatorComponents, associator, whiskerLeft, whiskerRight,
             chosenCoend.map]; done)
         | (simp [associatorComponents, associator, whiskerLeft, whiskerRight]; done)
         | (simp [associatorComponents]; rfl))
    | (obtain ⟨j, y, rfl⟩ := Types.jointly_surjective' x
       first
         | rfl
         | (simp [associatorComponents, associator, whiskerLeft, whiskerRight]; done))
