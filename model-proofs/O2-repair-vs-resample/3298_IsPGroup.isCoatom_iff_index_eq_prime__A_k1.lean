/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     IsPGroup.isCoatom_iff_index_eq_prime
Source:      Mathlib @ a02a63c2, Mathlib/GroupTheory/Nilpotent.lean, line 1261
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  O2-repair-vs-resample, arm A, attempt 1, verified in round 0 (round 0 = first attempt)
Prover:      claude-opus-5-5
Setup:       Opus 5.5: arm B = one attempt plus up to 3 repair rounds with Lean error messages; arm A = 4 independent attempts (attempt k)
Check:       the proof replaced the human proof in the Mathlib file above; Lean reported
             0 errors and no `sorry`; sorry/admit/native_decide/search tactics were rejected.
-/

-- (context: the Mathlib file above this declaration)
theorem isCoatom_iff_index_eq_prime [Group.IsNilpotent G] (hG : IsPGroup p G) {H : Subgroup G} :
    IsCoatom H ↔ H.index = p := by
  rw [Subgroup.isCoatom_iff_index_prime]
  constructor
  · intro h
    haveI : H.FiniteIndex := ⟨h.ne_zero⟩
    obtain ⟨n, hn⟩ := hG.index H
    rcases n with _ | n
    · rw [hn, pow_zero] at h
      exact absurd h Nat.not_prime_one
    · have hd : p ∣ H.index := by
        rw [hn]
        exact dvd_pow_self p n.succ_ne_zero
      exact ((Nat.prime_dvd_prime_iff_eq hp.out h).mp hd).symm
  · intro h
    rw [h]
    exact hp.out
