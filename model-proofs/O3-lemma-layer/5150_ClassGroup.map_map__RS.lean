/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     ClassGroup.map_map
Source:      Mathlib @ a02a63c2, Mathlib/RingTheory/ClassGroup/ExtendedHom.lean, line 84
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  O3-lemma-layer, arm RS, verified in round 0 (round 0 = first attempt)
Prover:      claude-opus-5-5
Setup:       Opus 5.5 with repair loop: arm R = repair only; arm RS = repair plus the Lean-checked lemma layer
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
  obtain ⟨α, rfl⟩ := QuotientGroup.mk_surjective x
  rw [map_quotientMk, map_quotientMk, map_quotientMk]
  congr 1
  ext : 1
  simp only [Units.coe_map, MonoidHom.coe_coe]
  first
    | rfl
    | simp [FractionalIdeal.extendedHom'_apply, FractionalIdeal.extended_extended]
    | (ext y; simp [FractionalIdeal.extendedHom'_apply])
    | simp [FractionalIdeal.extendedHom']
