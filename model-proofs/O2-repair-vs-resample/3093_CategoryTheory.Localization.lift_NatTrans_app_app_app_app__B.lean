/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     CategoryTheory.Localization.lift₄NatTrans_app_app_app_app
Source:      Mathlib @ a02a63c2, Mathlib/CategoryTheory/Localization/Quadrifunctor.lean, line 123
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  O2-repair-vs-resample, arm B, verified in round 1 (round 0 = first attempt)
Prover:      claude-opus-5-5
Setup:       Opus 5.5: arm B = one attempt plus up to 3 repair rounds with Lean error messages; arm A = 4 independent attempts (attempt k)
Check:       the proof replaced the human proof in the Mathlib file above; Lean reported
             0 errors and no `sorry`; sorry/admit/native_decide/search tactics were rejected.
-/

-- (context: the Mathlib file above this declaration)
@[simp]
theorem lift₄NatTrans_app_app_app_app (X₁ : C₁) (X₂ : C₂) (X₃ : C₃) (X₄ : C₄) :
    ((((lift₄NatTrans L₁ L₂ L₃ L₄ W₁ W₂ W₃ W₄ F₁ F₂ F₁' F₂' τ).app
      (L₁.obj X₁)).app (L₂.obj X₂)).app (L₃.obj X₃)).app (L₄.obj X₄) =
        ((((Lifting₄.iso L₁ L₂ L₃ L₄ W₁ W₂ W₃ W₄ F₁ F₁').hom.app X₁).app X₂).app X₃).app X₄ ≫
          (((τ.app X₁).app X₂).app X₃).app X₄ ≫
          ((((Lifting₄.iso L₁ L₂ L₃ L₄ W₁ W₂ W₃ W₄ F₂ F₂').inv.app X₁).app X₂).app X₃).app X₄ := by
  have h := liftNatTrans_app (L₁.prod (L₂.prod (L₃.prod L₄)))
      (W₁.prod (W₂.prod (W₃.prod W₄)))
      (uncurry₄.obj F₁) (uncurry₄.obj F₂) (uncurry₄.obj F₁') (uncurry₄.obj F₂')
      (uncurry₄.map τ) ⟨X₁, X₂, X₃, X₄⟩
  have h' := congr_app (Functor.FullyFaithful.map_preimage fullyFaithfulUncurry₄
    (liftNatTrans (L₁.prod (L₂.prod (L₃.prod L₄))) (W₁.prod (W₂.prod (W₃.prod W₄)))
      (uncurry₄.obj F₁) (uncurry₄.obj F₂) (uncurry₄.obj F₁') (uncurry₄.obj F₂')
      (uncurry₄.map τ))) (L₁.obj X₁, L₂.obj X₂, L₃.obj X₃, L₄.obj X₄)
  first
    | exact h'.trans h
    | (have h'' := h'.trans h
       simpa using h'')
    | (have h'' := h'.trans h
       simp only [lift₄NatTrans]
       simpa using h'')
