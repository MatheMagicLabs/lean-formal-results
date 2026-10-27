/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     CochainComplex.HomComplex.Cocycle.fromSingleMk_smul
Source:      Mathlib @ a02a63c2, Mathlib/Algebra/Homology/HomotopyCategory/HomComplexSingle.lean, line 314
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  O4-layer-with-search, arm RT, verified in round 0 (round 0 = first attempt)
Prover:      claude-opus-5-5
Setup:       Opus 5.5 with repair loop, lemma layer and name search (arm RT)
Check:       the proof replaced the human proof in the Mathlib file above; Lean reported
             0 errors and no `sorry`; sorry/admit/native_decide/search tactics were rejected.
-/

open CategoryTheory Category Limits Preadditive
universe v u
variable {C : Type u} [Category.{v} C] [Preadditive C] [HasZeroObject C]
namespace CochainComplex
namespace HomComplex
variable {X : C} {K : CochainComplex C ℤ}
namespace Cochain
variable (X K) in
variable (X K) in
end Cochain
namespace Cocycle

lemma fromSingleMk_smul {R : Type*} [Ring R] [Linear R C]
    (r : R) {p q : ℤ} (f : X ⟶ K.X q) {n : ℤ} (h : p + n = q)
    (q' : ℤ) (hq' : q + 1 = q') (hf : f ≫ K.d q q' = 0) :
    fromSingleMk (r • f) h q' hq' (by simp [hf]) = r • fromSingleMk f h q' hq' hf := by
  apply Cocycle.ext
  rw [Cocycle.coe_smul]
  exact Cochain.fromSingleMk_smul r f h
