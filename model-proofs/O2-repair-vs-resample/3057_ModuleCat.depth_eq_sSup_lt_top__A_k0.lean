/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     ModuleCat.depth_eq_sSup_lt_top
Source:      Mathlib @ a02a63c2, Mathlib/RingTheory/Depth/Basic.lean, line 144
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  O2-repair-vs-resample, arm A, attempt 0, verified in round 0 (round 0 = first attempt)
Prover:      claude-opus-5-5
Setup:       Opus 5.5: arm B = one attempt plus up to 3 repair rounds with Lean error messages; arm A = 4 independent attempts (attempt k)
Check:       the proof replaced the human proof in the Mathlib file above; Lean reported
             0 errors and no `sorry`; sorry/admit/native_decide/search tactics were rejected.
-/

-- (context: the Mathlib file above this declaration)
lemma depth_eq_sSup_lt_top (N M : ModuleCat.{v} R) : N.depth M =
    sSup {n : ℕ∞ | n < ⊤ ∧ ∀ i : ℕ, i < n → Subsingleton (Ext N M i)} := by
  unfold depth
  apply le_antisymm
  · apply sSup_le
    intro n hn
    by_cases h : n < ⊤
    · exact le_sSup ⟨h, hn⟩
    · have h' : n = ⊤ := by simpa using h
      have hn' : ∀ i : ℕ, Subsingleton (Ext N M i) := fun i => hn i (by simp [h'])
      have hT : sSup {n : ℕ∞ | n < ⊤ ∧ ∀ i : ℕ, i < n → Subsingleton (Ext N M i)} = ⊤ := by
        by_contra hne
        obtain ⟨k, hk⟩ := ENat.ne_top_iff_exists.mp hne
        have : ((k + 1 : ℕ) : ℕ∞) ≤ (k : ℕ∞) := by
          rw [hk]
          exact le_sSup ⟨by simp, fun i _ => hn' i⟩
        norm_cast at this
        omega
      rw [hT]
      exact le_top
  · exact sSup_le_sSup (fun n hn => hn.2)
