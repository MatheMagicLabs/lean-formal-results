/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     CategoryTheory.Localization.lift₄NatTrans_app_app_app_app
Source:      Mathlib @ a02a63c2, Mathlib/CategoryTheory/Localization/Quadrifunctor.lean, line 123
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  O2-repair-vs-resample, arm A, attempt 0, verified in round 0 (round 0 = first attempt)
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
  have h := liftNatTrans_app (L₁.prod (L₂.prod (L₃.prod L₄))) (W₁.prod (W₂.prod (W₃.prod W₄)))
      (uncurry₄.obj F₁) (uncurry₄.obj F₂) (uncurry₄.obj F₁') (uncurry₄.obj F₂')
      (uncurry₄.map τ) (X₁, X₂, X₃, X₄)
  have h' : uncurry₄.map (lift₄NatTrans L₁ L₂ L₃ L₄ W₁ W₂ W₃ W₄ F₁ F₂ F₁' F₂' τ) =
      liftNatTrans (L₁.prod (L₂.prod (L₃.prod L₄))) (W₁.prod (W₂.prod (W₃.prod W₄)))
        (uncurry₄.obj F₁) (uncurry₄.obj F₂) (uncurry₄.obj F₁') (uncurry₄.obj F₂')
        (uncurry₄.map τ) :=
    fullyFaithfulUncurry₄.map_preimage _
  rw [← h'] at h
  first
  | exact h
  | simpa [uncurry₄, Lifting₄.uncurry] using h
