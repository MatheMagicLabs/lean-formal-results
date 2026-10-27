/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     CategoryTheory.NatTrans.mapHomotopyCategoryPlus_id
Source:      Mathlib @ a02a63c2, Mathlib/Algebra/Homology/HomotopyCategory/Plus.lean, line 414
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  A2-astra-effort-low, arm R, verified in round 1 (round 0 = first attempt)
Prover:      gpt-6-astra
Setup:       GPT-6 Astra, reasoning effort low (arms R, N0)
Check:       the proof replaced the human proof in the Mathlib file above; Lean reported
             0 errors and no `sorry`; sorry/admit/native_decide/search tactics were rejected.
-/

open CategoryTheory Limits ZeroObject Pretriangulated HomotopicalAlgebra
variable (C D : Type*) [Category* C] [Category* D] [Preadditive C] [Preadditive D]
namespace CochainComplex
open HomologicalComplex
variable {C} [HasBinaryBiproducts C]
set_option backward.defeqAttrib.useBackward true in
end CochainComplex
namespace HomotopyCategory
variable {C} in
set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
namespace Plus
variable {C} in
section
variable [HasZeroObject C] [HasBinaryBiproducts C]
set_option backward.isDefEq.respectTransparency.types false in
open HomologicalComplex in
set_option backward.defeqAttrib.useBackward true in
open HomologicalComplex in
end
end Plus
end HomotopyCategory
namespace CategoryTheory
namespace Functor
variable {C D}
variable (F : C ⥤ D) [F.Additive]
set_option backward.isDefEq.respectTransparency.types false in
end Functor
namespace NatTrans
variable {C D} {F₁ F₂ F₃ : C ⥤ D} [F₁.Additive] [F₂.Additive] [F₃.Additive]
variable (F₁) in

@[simp]
lemma mapHomotopyCategoryPlus_id :
    NatTrans.mapHomotopyCategoryPlus (𝟙 F₁) = 𝟙 _ := by
  ext X
  simp [NatTrans.mapHomotopyCategoryPlus]
  rfl
