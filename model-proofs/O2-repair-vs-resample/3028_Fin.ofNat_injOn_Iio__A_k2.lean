/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     Fin.ofNat_injOn_Iio
Source:      Mathlib @ a02a63c2, Mathlib/Order/Interval/Set/Fin.lean, line 100
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  O2-repair-vs-resample, arm A, attempt 2, verified in round 0 (round 0 = first attempt)
Prover:      claude-opus-5-5
Setup:       Opus 5.5: arm B = one attempt plus up to 3 repair rounds with Lean error messages; arm A = 4 independent attempts (attempt k)
Check:       the proof replaced the human proof in the Mathlib file above; Lean reported
             0 errors and no `sorry`; sorry/admit/native_decide/search tactics were rejected.
-/

-- (context: the Mathlib file above this declaration)
lemma ofNat_injOn_Iio {n m : ℕ} [NeZero n] (hmn : m ≤ n) :
    Set.InjOn (Fin.ofNat n) (Set.Iio m) := by
  intro a ha b hb h
  have ha' : a < n := lt_of_lt_of_le (Set.mem_Iio.mp ha) hmn
  have hb' : b < n := lt_of_lt_of_le (Set.mem_Iio.mp hb) hmn
  have h2 := congrArg Fin.val h
  change a % n = b % n at h2
  rwa [Nat.mod_eq_of_lt ha', Nat.mod_eq_of_lt hb'] at h2
