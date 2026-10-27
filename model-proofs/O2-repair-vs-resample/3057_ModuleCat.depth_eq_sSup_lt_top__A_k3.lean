/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     ModuleCat.depth_eq_sSup_lt_top
Source:      Mathlib @ a02a63c2, Mathlib/RingTheory/Depth/Basic.lean, line 144
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  O2-repair-vs-resample, arm A, attempt 3, verified in round 0 (round 0 = first attempt)
Prover:      claude-opus-5-5
Setup:       Opus 5.5: arm B = one attempt plus up to 3 repair rounds with Lean error messages; arm A = 4 independent attempts (attempt k)
Check:       the proof replaced the human proof in the Mathlib file above; Lean reported
             0 errors and no `sorry`; sorry/admit/native_decide/search tactics were rejected.
-/

-- (context: the Mathlib file above this declaration)
lemma depth_eq_sSup_lt_top (N M : ModuleCat.{v} R) : N.depth M =
    sSup {n : ℕ∞ | n < ⊤ ∧ ∀ i : ℕ, i < n → Subsingleton (Ext N M i)} := by
  show sSup _ = _
  apply le_antisymm
  · apply sSup_le
    intro n hn
    by_cases h : n = ⊤
    · subst h
      apply le_of_forall_lt
      intro c hc
      lift c to ℕ using hc.ne
      exact lt_of_lt_of_le (Nat.cast_lt.mpr (Nat.lt_add_one c))
        (le_sSup ⟨ENat.coe_lt_top _, fun i _ ↦ hn i (ENat.coe_lt_top i)⟩)
    · exact le_sSup ⟨lt_top_iff_ne_top.mpr h, hn⟩
  · exact sSup_le_sSup (fun n hn ↦ hn.2)
