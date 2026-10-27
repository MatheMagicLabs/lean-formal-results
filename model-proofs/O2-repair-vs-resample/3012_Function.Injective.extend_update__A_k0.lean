/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     Function.Injective.extend_update
Source:      Mathlib @ a02a63c2, Mathlib/Logic/Function/Basic.lean, line 916
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  O2-repair-vs-resample, arm A, attempt 0, verified in round 0 (round 0 = first attempt)
Prover:      claude-opus-5-5
Setup:       Opus 5.5: arm B = one attempt plus up to 3 repair rounds with Lean error messages; arm A = 4 independent attempts (attempt k)
Check:       the proof replaced the human proof in the Mathlib file above; Lean reported
             0 errors and no `sorry`; sorry/admit/native_decide/search tactics were rejected.
-/

-- (context: the Mathlib file above this declaration)
theorem Injective.extend_update [DecidableEq α] [DecidableEq β] (hf : Injective f) (g : α → γ)
    (e : β → γ) (i : α) (a : γ) :
    extend f (update g i a) e = update (extend f g e) (f i) a := by
  ext b
  by_cases h : ∃ x, f x = b
  · obtain ⟨x, rfl⟩ := h
    rw [hf.extend_apply]
    by_cases hx : x = i
    · subst hx; simp
    · rw [update_of_ne hx, update_of_ne (hf.ne hx), hf.extend_apply]
  · rw [extend_apply' _ _ _ h, update_of_ne, extend_apply' _ _ _ h]
    rintro rfl
    exact h ⟨i, rfl⟩
