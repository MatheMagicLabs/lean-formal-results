/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     CochainComplex.HomComplex.Cocycle.toSingleMk_smul
Source:      Mathlib @ a02a63c2, Mathlib/Algebra/Homology/HomotopyCategory/HomComplexSingle.lean, line 398
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  E1-repair-decomposition, arm Z, verified in round 1 (round 0 = first attempt)
Prover:      gpt-6-astra
Setup:       GPT-6 Astra, which part of Lean feedback makes repair work: after a shared first attempt (E0), V = full error messages, Z = line numbers only, B = only "Lean rejected this proof"
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
variable (X K) in

lemma toSingleMk_smul {R : Type*} [Ring R] [Linear R C]
    (r : R) {p q : ℤ} (f : K.X p ⟶ X) {n : ℤ} (h : p + n = q)
    (p' : ℤ) (hp' : p' + 1 = p) (hf : K.d p' p ≫ f = 0) :
    toSingleMk (r • f) h p' hp' (by simp [hf]) = r • toSingleMk f h p' hp' hf := by
  ext : 1
  exact Cochain.toSingleMk_smul r f h
