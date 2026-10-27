/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     ModuleCat.depth_eq_sSup_lt_top
Source:      Mathlib @ a02a63c2, Mathlib/RingTheory/Depth/Basic.lean, line 144
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  O5-repair-sonnet, arm A, attempt 1, verified in round 0 (round 0 = first attempt)
Prover:      claude-sonnet-5-5
Setup:       Sonnet 5.5: arm B = repair loop; arm A = independent attempts
Check:       the proof replaced the human proof in the Mathlib file above; Lean reported
             0 errors and no `sorry`; sorry/admit/native_decide/search tactics were rejected.
-/

-- (context: the Mathlib file above this declaration)
lemma depth_eq_sSup_lt_top (N M : ModuleCat.{v} R) : N.depth M =
    sSup {n : ℕ∞ | n < ⊤ ∧ ∀ i : ℕ, i < n → Subsingleton (Ext N M i)} := by
  by_cases h : N.depth M = ⊤
  · rw [h]
    have hall := (depth_eq_top_iff N M).mp h
    symm
    by_contra hne
    obtain ⟨m, hm⟩ := ENat.ne_top_iff_exists.mp hne
    have hle : ((m + 1 : ℕ) : ℕ∞) ≤
        sSup {n : ℕ∞ | n < ⊤ ∧ ∀ i : ℕ, i < n → Subsingleton (Ext N M i)} :=
      le_sSup ⟨ENat.coe_lt_top _, fun i _ => hall i⟩
    rw [← hm] at hle
    have : m + 1 ≤ m := by exact_mod_cast hle
    omega
  · apply le_antisymm
    · exact le_sSup ⟨lt_top_iff_ne_top.mpr h, fun i hi => subsingleton_ext_of_lt_depth hi⟩
    · unfold ModuleCat.depth
      apply sSup_le_sSup
      intro n hn
      exact hn.2
