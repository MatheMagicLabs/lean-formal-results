/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     Polynomial.dvd_of_mem_sturmSeq
Source:      Mathlib @ a02a63c2, Mathlib/Algebra/Polynomial/Sturm/Sequence.lean, line 127
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  O2-repair-vs-resample, arm A, attempt 3, verified in round 0 (round 0 = first attempt)
Prover:      claude-opus-5-5
Setup:       Opus 5.5: arm B = one attempt plus up to 3 repair rounds with Lean error messages; arm A = 4 independent attempts (attempt k)
Check:       the proof replaced the human proof in the Mathlib file above; Lean reported
             0 errors and no `sorry`; sorry/admit/native_decide/search tactics were rejected.
-/

-- (context: the Mathlib file above this declaration)
lemma dvd_of_mem_sturmSeq {d p q s : K[X]} (hp : d ∣ p) (hq : d ∣ q)
    (hs : s ∈ sturmSeq p q) : d ∣ s := by
  revert hp hq hs
  induction p, q using sturmSeq.induct
  next q =>
    intro _ _ hs
    simp at hs
  next p q hp0 ih =>
    intro hp hq hs
    rw [sturmSeq_cons hp0] at hs
    rcases List.mem_cons.mp hs with h | hs
    · rw [h]; exact hp
    · have h := EuclideanDomain.div_add_mod (-p) q
      have key : d ∣ -p - q * (-p / q) := (dvd_neg.mpr hp).sub (hq.mul_right _)
      have hm : d ∣ -p % q := by
        convert key using 1
        exact eq_sub_of_add_eq' h
      exact ih hq hm hs
