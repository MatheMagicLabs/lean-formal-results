/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     ModuleCat.depth_eq_iff
Source:      Mathlib @ a02a63c2, Mathlib/RingTheory/Depth/Basic.lean, line 124
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  O2-repair-vs-resample, arm A, attempt 1, verified in round 0 (round 0 = first attempt)
Prover:      claude-opus-5-5
Setup:       Opus 5.5: arm B = one attempt plus up to 3 repair rounds with Lean error messages; arm A = 4 independent attempts (attempt k)
Check:       the proof replaced the human proof in the Mathlib file above; Lean reported
             0 errors and no `sorry`; sorry/admit/native_decide/search tactics were rejected.
-/

-- (context: the Mathlib file above this declaration)
lemma depth_eq_iff (N M : ModuleCat.{v} R) (n : ℕ) : N.depth M = n ↔
    Nontrivial (Ext N M n) ∧ ∀ i < n, Subsingleton (Ext N M i) := by
  classical
  constructor
  · intro hd
    have hlt : N.depth M < ⊤ := by rw [hd]; exact ENat.coe_lt_top n
    have h := (depth_lt_top_iff N M).mp hlt
    rw [depth_eq_find N M h] at hd
    have hn : Nat.find h = n := by exact_mod_cast hd
    subst hn
    refine ⟨Nat.find_spec h, fun i hi => ?_⟩
    exact not_nontrivial_iff_subsingleton.mp (Nat.find_min h hi)
  · rintro ⟨hn, hi⟩
    have h : ∃ n, Nontrivial (Ext N M n) := ⟨n, hn⟩
    rw [depth_eq_find N M h]
    have : Nat.find h = n := (Nat.find_eq_iff h).mpr
      ⟨hn, fun i hi' => not_nontrivial_iff_subsingleton.mpr (hi i hi')⟩
    rw [this]
