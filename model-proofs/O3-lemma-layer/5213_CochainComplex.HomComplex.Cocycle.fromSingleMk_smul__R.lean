/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     CochainComplex.HomComplex.Cocycle.fromSingleMk_smul
Source:      Mathlib @ a02a63c2, Mathlib/Algebra/Homology/HomotopyCategory/HomComplexSingle.lean, line 314
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  O3-lemma-layer, arm R, verified in round 0 (round 0 = first attempt)
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

lemma fromSingleMk_smul {R : Type*} [Ring R] [Linear R C]
    (r : R) {p q : ℤ} (f : X ⟶ K.X q) {n : ℤ} (h : p + n = q)
    (q' : ℤ) (hq' : q + 1 = q') (hf : f ≫ K.d q q' = 0) :
    fromSingleMk (r • f) h q' hq' (by simp [hf]) = r • fromSingleMk f h q' hq' hf := by
  apply Cocycle.ext
  first
  | exact Cochain.fromSingleMk_smul r f h
  | (simp [fromSingleMk, Cochain.fromSingleMk_smul]; done)
  | (dsimp only [fromSingleMk]
     simp only [Cocycle.coe_smul]
     ext i j hij
     by_cases hi : i = p
     · subst hi
       obtain rfl : j = q := by omega
       simp [Cochain.fromSingleMk_v]
     · apply IsZero.eq_of_src
       exact HomologicalComplex.isZero_single_obj_X _ _ _ _ hi)
