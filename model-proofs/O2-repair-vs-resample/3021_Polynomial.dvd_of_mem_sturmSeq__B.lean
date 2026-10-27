/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     Polynomial.dvd_of_mem_sturmSeq
Source:      Mathlib @ a02a63c2, Mathlib/Algebra/Polynomial/Sturm/Sequence.lean, line 127
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  O2-repair-vs-resample, arm B, verified in round 1 (round 0 = first attempt)
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
  next => simp_all
  next p q hp0 ih =>
    intro hp hq hs
    rw [sturmSeq_cons hp0] at hs
    rcases List.mem_cons.mp hs with rfl | hs
    · exact hp
    · have h2 : d ∣ q * (-p / q) + -p % q := by
        have h3 := dvd_neg.mpr hp
        rwa [← EuclideanDomain.div_add_mod (-p) q] at h3
      exact ih hq ((dvd_add_right (dvd_mul_of_dvd_left hq _)).mp h2) hs
