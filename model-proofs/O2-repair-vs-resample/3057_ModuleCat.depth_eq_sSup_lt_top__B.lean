/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     ModuleCat.depth_eq_sSup_lt_top
Source:      Mathlib @ a02a63c2, Mathlib/RingTheory/Depth/Basic.lean, line 144
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  O2-repair-vs-resample, arm B, verified in round 0 (round 0 = first attempt)
Prover:      claude-opus-5-5
Setup:       Opus 5.5: arm B = one attempt plus up to 3 repair rounds with Lean error messages; arm A = 4 independent attempts (attempt k)
Check:       the proof replaced the human proof in the Mathlib file above; Lean reported
             0 errors and no `sorry`; sorry/admit/native_decide/search tactics were rejected.
-/

-- (context: the Mathlib file above this declaration)
lemma depth_eq_sSup_lt_top (N M : ModuleCat.{v} R) : N.depth M =
    sSup {n : ℕ∞ | n < ⊤ ∧ ∀ i : ℕ, i < n → Subsingleton (Ext N M i)} := by
  apply le_antisymm
  · unfold ModuleCat.depth
    apply sSup_le
    intro n hn
    rw [Set.mem_setOf_eq] at hn
    by_cases h : n < ⊤
    · exact le_sSup ⟨h, hn⟩
    · have htop : n = ⊤ := top_le_iff.mp (not_lt.mp h)
      subst htop
      have hall : ∀ m : ℕ, (m : ℕ∞) ≤
          sSup {n : ℕ∞ | n < ⊤ ∧ ∀ i : ℕ, i < n → Subsingleton (Ext N M i)} :=
        fun m => le_sSup ⟨ENat.coe_lt_top m, fun i hi => hn i (lt_of_lt_of_le hi le_top)⟩
      by_contra hne
      obtain ⟨k, hk⟩ := ENat.ne_top_iff_exists.mp (ne_top_of_lt (lt_of_not_ge hne))
      have := hall (k + 1)
      rw [← hk] at this
      have := Nat.cast_le.mp this
      omega
  · unfold ModuleCat.depth
    apply sSup_le_sSup
    intro n hn
    exact hn.2
