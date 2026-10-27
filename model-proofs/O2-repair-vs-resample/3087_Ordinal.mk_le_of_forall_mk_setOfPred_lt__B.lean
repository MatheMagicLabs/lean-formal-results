/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     Ordinal.mk_le_of_forall_mk_setOfPred_lt
Source:      Mathlib @ a02a63c2, Mathlib/SetTheory/Ordinal/Basic.lean, line 515
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  O2-repair-vs-resample, arm B, verified in round 0 (round 0 = first attempt)
Prover:      claude-opus-5-5
Setup:       Opus 5.5: arm B = one attempt plus up to 3 repair rounds with Lean error messages; arm A = 4 independent attempts (attempt k)
Check:       the proof replaced the human proof in the Mathlib file above; Lean reported
             0 errors and no `sorry`; sorry/admit/native_decide/search tactics were rejected.
-/

-- (context: the Mathlib file above this declaration)
theorem mk_le_of_forall_mk_setOfPred_lt {α β : Type u} {c : Cardinal}
    [LinearOrder β] [WellFoundedLT β] (f : α → β) (hf : Function.Injective f)
    (H : ∀ x, #{y | f y < f x} < c) : #α ≤ c := by
  let r' : α → α → Prop := fun a b => f a < f b
  have hwo : IsWellOrder α r' :=
    (RelEmbedding.preimage ⟨f, hf⟩ (· < · : β → β → Prop)).isWellOrder
  rcases le_or_gt (type r') (type (@WellOrderingRel c.out)) with h | h
  · have := card_le_card h
    rwa [card_type, card_type, mk_out] at this
  · obtain ⟨x, hx⟩ := typein_surj r' h
    have h1 := card_typein (r := r') x
    rw [hx, card_type, mk_out] at h1
    exact absurd h1.symm (H x).ne
