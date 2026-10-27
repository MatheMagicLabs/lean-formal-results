/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     ClassGroup.map_map
Source:      Mathlib @ a02a63c2, Mathlib/RingTheory/ClassGroup/ExtendedHom.lean, line 84
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  A2-astra-effort-high, arm R, verified in round 3 (round 0 = first attempt)
Prover:      gpt-6-astra
Setup:       GPT-6 Astra, reasoning effort high (arms R, N0)
Check:       the proof replaced the human proof in the Mathlib file above; Lean reported
             0 errors and no `sorry`; sorry/admit/native_decide/search tactics were rejected.
-/

open scoped nonZeroDivisors
namespace ClassGroup
section Map
variable {A B C : Type*} [CommRing A] [IsDomain A] [CommRing B] [IsDomain B] [CommRing C]

theorem map_map (f : A →+* B) (hf : Function.Injective f) (g : B →+* C)
    (hg : Function.Injective g) (x : ClassGroup A) :
    map g hg (map f hf x) = map (g.comp f) (hg.comp hf) x := by
  classical
  induction x using Quotient.inductionOn with
  | h I =>
    change (⟦_⟧ : ClassGroup C) = ⟦_⟧
    apply congrArg (Quotient.mk _)
    apply Units.ext
    simp only [Units.coe_map, FractionalIdeal.extendedHom',
      FractionalIdeal.extendedHom, MonoidHom.coe_mk, OneHom.coe_mk]
    apply FractionalIdeal.extended_extended
