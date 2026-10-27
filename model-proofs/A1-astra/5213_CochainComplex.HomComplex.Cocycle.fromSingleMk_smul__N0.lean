/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     CochainComplex.HomComplex.Cocycle.fromSingleMk_smul
Source:      Mathlib @ a02a63c2, Mathlib/Algebra/Homology/HomotopyCategory/HomComplexSingle.lean, line 314
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  A1-astra, arm N0, verified in round 0 (round 0 = first attempt)
Prover:      gpt-6-astra
Setup:       GPT-6 Astra (Codex, effort medium): R = proof plus up to 3 repair rounds with Lean errors; RS = R plus lemma layer; RT = R with read-only Mathlib sources to search; N0-N3 = independent attempts
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
  apply Subtype.ext
  exact Cochain.fromSingleMk_smul r f h
