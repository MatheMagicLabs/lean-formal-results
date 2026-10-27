/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     Ordinal.mk_le_of_forall_mk_setOfPred_lt
Source:      Mathlib @ a02a63c2, Mathlib/SetTheory/Ordinal/Basic.lean, line 515
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  O2-repair-vs-resample, arm A, attempt 1, verified in round 0 (round 0 = first attempt)
Prover:      claude-opus-5-5
Setup:       Opus 5.5: arm B = one attempt plus up to 3 repair rounds with Lean error messages; arm A = 4 independent attempts (attempt k)
Check:       the proof replaced the human proof in the Mathlib file above; Lean reported
             0 errors and no `sorry`; sorry/admit/native_decide/search tactics were rejected.
-/

-- (context: the Mathlib file above this declaration)
theorem mk_le_of_forall_mk_setOfPred_lt {α β : Type u} {c : Cardinal}
    [LinearOrder β] [WellFoundedLT β] (f : α → β) (hf : Function.Injective f)
    (H : ∀ x, #{y | f y < f x} < c) : #α ≤ c := by
  classical
  by_contra! hc
  obtain ⟨T, hT⟩ := Cardinal.le_mk_iff_exists_set.1 hc.le
  let g : α ↪ β := ⟨f, hf⟩
  haveI : IsWellOrder α (g ⁻¹'o (· < · : β → β → Prop)) :=
    (RelEmbedding.preimage g (· < · : β → β → Prop)).isWellOrder
  have hle : type (Subrel (g ⁻¹'o (· < · : β → β → Prop)) (· ∈ T))
      ≤ type (g ⁻¹'o (· < · : β → β → Prop)) :=
    (Subrel.relEmbedding _ _).ordinal_type_le
  rcases hle.lt_or_eq with h | h
  · obtain ⟨x, hx⟩ := typein_surj _ h
    have := congrArg card hx
    rw [card_typein, card_type] at this
    exact (H x).ne (this.trans hT)
  · have := congrArg card h
    rw [card_type, card_type] at this
    exact hc.ne (hT.symm.trans this)
