/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     Polynomial.mul_mod_mul_left
Source:      Mathlib @ a02a63c2, Mathlib/Algebra/Polynomial/FieldDivision.lean, line 738
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  O2-repair-vs-resample, arm A, attempt 2, verified in round 0 (round 0 = first attempt)
Prover:      claude-opus-5-5
Setup:       Opus 5.5: arm B = one attempt plus up to 3 repair rounds with Lean error messages; arm A = 4 independent attempts (attempt k)
Check:       the proof replaced the human proof in the Mathlib file above; Lean reported
             0 errors and no `sorry`; sorry/admit/native_decide/search tactics were rejected.
-/

-- (context: the Mathlib file above this declaration)
theorem mul_mod_mul_left {p₁ p₂ q : R[X]} : (q * p₁) % (q * p₂) = q * (p₁ % p₂) := by
  rcases eq_or_ne q 0 with rfl | hq
  · simp
  rcases eq_or_ne p₂ 0 with rfl | hp₂
  · simp [mod_def]
  have h : (q * p₁) % (q * p₂) = (q * (p₁ % p₂)) % (q * p₂) := by
    apply mod_eq_of_dvd_sub
    refine ⟨p₁ / p₂, ?_⟩
    have := EuclideanDomain.div_add_mod p₁ p₂
    rw [← mul_sub, mul_assoc]
    congr 1
    rw [sub_eq_iff_eq_add]
    exact this.symm
  rw [h, mod_eq_self_iff (mul_ne_zero hq hp₂), degree_mul, degree_mul]
  first
    | exact WithBot.add_lt_add_left (degree_ne_bot.mpr hq) (degree_mod_lt p₁ hp₂)
    | (have h1 := degree_mod_lt p₁ hp₂
       rw [degree_eq_natDegree hq, degree_eq_natDegree hp₂] at *
       by_cases h0 : p₁ % p₂ = 0
       · simp only [h0, degree_zero]
         simp
       · rw [degree_eq_natDegree h0] at *
         exact_mod_cast (by
           have : (p₁ % p₂).natDegree < p₂.natDegree := by exact_mod_cast h1
           omega))
