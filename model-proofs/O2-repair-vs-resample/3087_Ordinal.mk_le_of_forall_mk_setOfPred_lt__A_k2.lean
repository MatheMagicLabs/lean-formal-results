/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     Ordinal.mk_le_of_forall_mk_setOfPred_lt
Source:      Mathlib @ a02a63c2, Mathlib/SetTheory/Ordinal/Basic.lean, line 515
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  O2-repair-vs-resample, arm A, attempt 2, verified in round 0 (round 0 = first attempt)
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
  obtain ⟨S, hS⟩ := Cardinal.le_mk_iff_exists_set.1 hc.le
  let r : α → α → Prop := fun a b => f a < f b
  let e : r ↪r ((· < ·) : β → β → Prop) := ⟨⟨f, hf⟩, fun {a b} => Iff.rfl⟩
  haveI : IsWellOrder α r := e.isWellOrder
  have hle : type (Subrel r (· ∈ S)) ≤ type r :=
    (Subrel.relEmbedding r (· ∈ S)).ordinal_type_le
  rcases hle.lt_or_eq with hlt | heq
  · obtain ⟨x, hx⟩ := typein_surj r hlt
    have h1 : #{y // r y x} = #{x // x ∈ S} := congrArg card hx
    exact (H x).ne (h1.trans hS)
  · have h1 : #{x // x ∈ S} = #α := congrArg card heq
    exact hc.ne (hS.symm.trans h1)
