/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     Fin.ofNat_injOn_Iio
Source:      Mathlib @ a02a63c2, Mathlib/Order/Interval/Set/Fin.lean, line 100
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  O5-repair-sonnet, arm A, attempt 0, verified in round 0 (round 0 = first attempt)
Prover:      claude-sonnet-5-5
Setup:       Sonnet 5.5: arm B = repair loop; arm A = independent attempts
Check:       the proof replaced the human proof in the Mathlib file above; Lean reported
             0 errors and no `sorry`; sorry/admit/native_decide/search tactics were rejected.
-/

-- (context: the Mathlib file above this declaration)
lemma ofNat_injOn_Iio {n m : ℕ} [NeZero n] (hmn : m ≤ n) :
    Set.InjOn (Fin.ofNat n) (Set.Iio m) := by
  intro a ha b hb h
  have ha' : a < n := lt_of_lt_of_le ha hmn
  have hb' : b < n := lt_of_lt_of_le hb hmn
  have h' : a % n = b % n := congrArg Fin.val h
  rwa [Nat.mod_eq_of_lt ha', Nat.mod_eq_of_lt hb'] at h'
