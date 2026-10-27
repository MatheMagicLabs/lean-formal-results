/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     Function.Injective.extend_update
Source:      Mathlib @ a02a63c2, Mathlib/Logic/Function/Basic.lean, line 916
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  O5-repair-sonnet, arm A, attempt 1, verified in round 0 (round 0 = first attempt)
Prover:      claude-sonnet-5-5
Setup:       Sonnet 5.5: arm B = repair loop; arm A = independent attempts
Check:       the proof replaced the human proof in the Mathlib file above; Lean reported
             0 errors and no `sorry`; sorry/admit/native_decide/search tactics were rejected.
-/

-- (context: the Mathlib file above this declaration)
theorem Injective.extend_update [DecidableEq α] [DecidableEq β] (hf : Injective f) (g : α → γ)
    (e : β → γ) (i : α) (a : γ) :
    extend f (update g i a) e = update (extend f g e) (f i) a := by
  funext b
  by_cases hb : ∃ a', f a' = b
  · obtain ⟨a', rfl⟩ := hb
    rw [hf.extend_apply]
    by_cases h : a' = i
    · subst h
      simp
    · rw [update_of_ne h, update_of_ne (hf.ne h), hf.extend_apply]
  · rw [extend_apply' _ _ _ hb, update_of_ne, extend_apply' _ _ _ hb]
    rintro rfl
    exact hb ⟨i, rfl⟩
