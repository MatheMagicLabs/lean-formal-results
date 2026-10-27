/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     Polynomial.dvd_of_mem_sturmSeq
Source:      Mathlib @ a02a63c2, Mathlib/Algebra/Polynomial/Sturm/Sequence.lean, line 127
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  O5-repair-sonnet, arm B, verified in round 2 (round 0 = first attempt)
Prover:      claude-sonnet-5-5
Setup:       Sonnet 5.5: arm B = repair loop; arm A = independent attempts
Check:       the proof replaced the human proof in the Mathlib file above; Lean reported
             0 errors and no `sorry`; sorry/admit/native_decide/search tactics were rejected.
-/

-- (context: the Mathlib file above this declaration)
lemma dvd_of_mem_sturmSeq {d p q s : K[X]} (hp : d ∣ p) (hq : d ∣ q)
    (hs : s ∈ sturmSeq p q) : d ∣ s := by
  revert hp hq hs
  induction p, q using sturmSeq.induct
  next q => intro hp hq hs; simp at hs
  next p q hp ih =>
    intro hdp hdq hs
    rw [sturmSeq_cons hp] at hs
    rcases List.mem_cons.mp hs with rfl | hs
    · exact hdp
    · have h : d ∣ -p % q := by
        rw [EuclideanDomain.mod_eq_sub_mul_div]
        exact dvd_sub (dvd_neg.mpr hdp) (dvd_mul_of_dvd_left hdq _)
      exact ih hdq h hs
