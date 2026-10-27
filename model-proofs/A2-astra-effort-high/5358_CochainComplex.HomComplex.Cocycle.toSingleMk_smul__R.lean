/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     CochainComplex.HomComplex.Cocycle.toSingleMk_smul
Source:      Mathlib @ a02a63c2, Mathlib/Algebra/Homology/HomotopyCategory/HomComplexSingle.lean, line 398
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  A2-astra-effort-high, arm R, verified in round 1 (round 0 = first attempt)
Prover:      gpt-6-astra
Setup:       GPT-6 Astra, reasoning effort high (arms R, N0)
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
  ext
  simp [toSingleMk, Cochain.toSingleMk, Cochain.single,
    Linear.smul_comp, Linear.comp_smul]
  <;> split_ifs <;> simp_all [Linear.smul_comp, Linear.comp_smul]
