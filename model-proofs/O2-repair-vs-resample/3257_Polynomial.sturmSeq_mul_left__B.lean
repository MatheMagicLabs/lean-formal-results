/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     Polynomial.sturmSeq_mul_left
Source:      Mathlib @ a02a63c2, Mathlib/Algebra/Polynomial/Sturm/Sequence.lean, line 139
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  O2-repair-vs-resample, arm B, verified in round 1 (round 0 = first attempt)
Prover:      claude-opus-5-5
Setup:       Opus 5.5: arm B = one attempt plus up to 3 repair rounds with Lean error messages; arm A = 4 independent attempts (attempt k)
Check:       the proof replaced the human proof in the Mathlib file above; Lean reported
             0 errors and no `sorry`; sorry/admit/native_decide/search tactics were rejected.
-/

-- (context: the Mathlib file above this declaration)
lemma sturmSeq_mul_left {r : K[X]} (hr : r ≠ 0) (p q : K[X]) :
    sturmSeq (r * p) (r * q) = (sturmSeq p q).map (r * ·) := by
  induction p, q using sturmSeq.induct
  next q => simp
  next p q hp ih =>
    have hrp : r * p ≠ 0 := mul_ne_zero hr hp
    have key : -(r * p) % (r * q) = r * (-p % q) := by
      by_cases hq : q = 0
      · subst hq
        simp [EuclideanDomain.mod_zero]
      · have hrq : r * q ≠ 0 := mul_ne_zero hr hq
        have h1 : r * q * (-(r * p) / (r * q)) + -(r * p) % (r * q) = -(r * p) :=
          EuclideanDomain.div_add_mod _ _
        have h2 : q * (-p / q) + -p % q = -p := EuclideanDomain.div_add_mod _ _
        have e1 : -(r * p) % (r * q) = -(r * p) - r * q * (-(r * p) / (r * q)) :=
          eq_sub_of_add_eq' h1
        have e2 : -p % q = -p - q * (-p / q) := eq_sub_of_add_eq' h2
        apply sub_eq_zero.mp
        have hdvd : r * q ∣ -(r * p) % (r * q) - r * (-p % q) := by
          refine ⟨-p / q - -(r * p) / (r * q), ?_⟩
          rw [e1, e2]
          ring
        have hX : degree (-(r * p) % (r * q)) < degree (r * q) := degree_mod_lt _ hrq
        have hY : degree (r * (-p % q)) < degree (r * q) := by
          by_cases hZ : -p % q = 0
          · rw [hZ, mul_zero, degree_zero]
            exact bot_lt_iff_ne_bot.mpr (fun h => hrq (degree_eq_bot.mp h))
          · apply degree_lt_degree
            rw [natDegree_mul hr hZ, natDegree_mul hr hq]
            have := natDegree_lt_natDegree hZ (degree_mod_lt (-p) hq)
            omega
        have hdeg : degree (-(r * p) % (r * q) - r * (-p % q)) < degree (r * q) :=
          lt_of_le_of_lt (degree_sub_le _ _) (max_lt hX hY)
        exact eq_zero_of_dvd_of_degree_lt hdvd hdeg
    rw [sturmSeq_cons hrp, sturmSeq_cons hp, key, ih]
    simp
