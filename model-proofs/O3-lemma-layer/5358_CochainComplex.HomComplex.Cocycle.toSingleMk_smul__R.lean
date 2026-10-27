/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     CochainComplex.HomComplex.Cocycle.toSingleMk_smul
Source:      Mathlib @ a02a63c2, Mathlib/Algebra/Homology/HomotopyCategory/HomComplexSingle.lean, line 398
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  O3-lemma-layer, arm R, verified in round 1 (round 0 = first attempt)
Prover:      claude-opus-5-5
Setup:       Opus 5.5 with repair loop: arm R = repair only; arm RS = repair plus the Lean-checked lemma layer
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
  apply Cocycle.ext
  first
  | exact Cochain.toSingleMk_smul r f h
  | (ext p'' q'' hpq
     simp only [toSingleMk, Cochain.toSingleMk, Cochain.smul_v, Cochain.mk_v] at *
     all_goals (try split_ifs) <;> (try subst_vars) <;>
       (try simp_all [Linear.smul_comp, Linear.comp_smul]))
  | (ext p'' q'' hpq
     simp [toSingleMk, Cochain.toSingleMk, Linear.smul_comp, Linear.comp_smul])
