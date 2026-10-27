/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     ModuleCat.depth_eq_iff
Source:      Mathlib @ a02a63c2, Mathlib/RingTheory/Depth/Basic.lean, line 124
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  O2-repair-vs-resample, arm A, attempt 2, verified in round 0 (round 0 = first attempt)
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
  · intro h
    have hlt : N.depth M < ⊤ := by rw [h]; exact ENat.coe_lt_top n
    obtain ex := (depth_lt_top_iff N M).mp hlt
    rw [depth_eq_find N M ex] at h
    have h' : Nat.find ex = n := by exact_mod_cast h
    rw [Nat.find_eq_iff] at h'
    exact ⟨h'.1, fun i hi => not_nontrivial_iff_subsingleton.mp (h'.2 i hi)⟩
  · rintro ⟨h1, h2⟩
    have ex : ∃ n, Nontrivial (Ext N M n) := ⟨n, h1⟩
    rw [depth_eq_find N M ex]
    have h' : Nat.find ex = n := by
      rw [Nat.find_eq_iff]
      exact ⟨h1, fun i hi => not_nontrivial_iff_subsingleton.mpr (h2 i hi)⟩
    exact_mod_cast h'
