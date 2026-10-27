/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     CategoryTheory.ProfCat.hom_ext
Source:      Mathlib @ a02a63c2, Mathlib/CategoryTheory/Profunctor/Bicategory.lean, line 105
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  O2-repair-vs-resample, arm A, attempt 2, verified in round 0 (round 0 = first attempt)
Prover:      claude-opus-5-5
Setup:       Opus 5.5: arm B = one attempt plus up to 3 repair rounds with Lean error messages; arm A = 4 independent attempts (attempt k)
Check:       the proof replaced the human proof in the Mathlib file above; Lean reported
             0 errors and no `sorry`; sorry/admit/native_decide/search tactics were rejected.
-/

-- (context: the Mathlib file above this declaration)
@[ext]
lemma hom_ext {η θ : P ⟶ Q}
    (h : ∀ (X : C) (Y : Dᵒᵖ) (x : (P.obj X).obj Y),
      (η.app X).app Y x = (θ.app X).app Y x) : η = θ := by
  first
    | exact NatTrans.ext (funext fun X => NatTrans.ext (funext fun Y => by ext x; exact h X Y x))
    | (refine NatTrans.ext ?_
       funext X
       refine NatTrans.ext ?_
       funext Y
       ext x
       exact h X Y x)
    | (ext X Y x
       exact h X Y x)
