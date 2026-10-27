/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     Polynomial.mul_mod_mul_left
Source:      Mathlib @ a02a63c2, Mathlib/Algebra/Polynomial/FieldDivision.lean, line 738
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  O2-repair-vs-resample, arm A, attempt 1, verified in round 0 (round 0 = first attempt)
Prover:      claude-opus-5-5
Setup:       Opus 5.5: arm B = one attempt plus up to 3 repair rounds with Lean error messages; arm A = 4 independent attempts (attempt k)
Check:       the proof replaced the human proof in the Mathlib file above; Lean reported
             0 errors and no `sorry`; sorry/admit/native_decide/search tactics were rejected.
-/

-- (context: the Mathlib file above this declaration)
theorem mul_mod_mul_left {p₁ p₂ q : R[X]} : (q * p₁) % (q * p₂) = q * (p₁ % p₂) := by
  by_cases hq : q = 0
  · simp [hq, mod_def]
  by_cases hp₂ : p₂ = 0
  · simp [hp₂, mod_def]
  have hqp : q * p₂ ≠ 0 := mul_ne_zero hq hp₂
  have h1 : (q * p₁) % (q * p₂) = (q * (p₁ % p₂)) % (q * p₂) := by
    apply mod_eq_of_dvd_sub
    refine ⟨p₁ / p₂, ?_⟩
    have := EuclideanDomain.div_add_mod p₁ p₂
    calc q * p₁ - q * (p₁ % p₂)
        = q * (p₂ * (p₁ / p₂) + p₁ % p₂) - q * (p₁ % p₂) := by rw [this]
      _ = q * p₂ * (p₁ / p₂) := by ring
  rw [h1, mod_eq_self_iff hqp, degree_mul, degree_mul]
  have h := degree_mod_lt p₁ hp₂
  first
  | exact WithBot.add_lt_add_left (degree_ne_bot.mpr hq) h
  | (rw [degree_eq_natDegree hq]; exact WithBot.add_lt_add_left WithBot.coe_ne_bot h)
