/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     ClassGroup.map_map
Source:      Mathlib @ a02a63c2, Mathlib/RingTheory/ClassGroup/ExtendedHom.lean, line 84
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  A1-astra, arm RS, verified in round 2 (round 0 = first attempt)
Prover:      gpt-6-astra
Setup:       GPT-6 Astra (Codex, effort medium): R = proof plus up to 3 repair rounds with Lean errors; RS = R plus lemma layer; RT = R with read-only Mathlib sources to search; N0-N3 = independent attempts
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
  induction x using QuotientGroup.induction_on with
  | H x =>
    simp only [map_quotientMk]
    congr 1
    apply Units.ext
    simp
    rw [FractionalIdeal.extended_extended]
