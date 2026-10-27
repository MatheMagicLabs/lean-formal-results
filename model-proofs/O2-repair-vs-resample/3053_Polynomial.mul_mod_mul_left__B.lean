/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     Polynomial.mul_mod_mul_left
Source:      Mathlib @ a02a63c2, Mathlib/Algebra/Polynomial/FieldDivision.lean, line 738
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  O2-repair-vs-resample, arm B, verified in round 1 (round 0 = first attempt)
Prover:      claude-opus-5-5
Setup:       Opus 5.5: arm B = one attempt plus up to 3 repair rounds with Lean error messages; arm A = 4 independent attempts (attempt k)
Check:       the proof replaced the human proof in the Mathlib file above; Lean reported
             0 errors and no `sorry`; sorry/admit/native_decide/search tactics were rejected.
-/

-- (context: the Mathlib file above this declaration)
theorem mul_mod_mul_left {p₁ p₂ q : R[X]} : (q * p₁) % (q * p₂) = q * (p₁ % p₂) := by
  by_cases hq : q = 0
  · simp [hq]
  by_cases hp : p₂ = 0
  · simp [hp, mod_def]
  rw [mod_eq_of_dvd_sub (p₂ := q * (p₁ % p₂))]
  · rw [mod_eq_self_iff (mul_ne_zero hq hp), degree_mul, degree_mul]
    have := degree_mod_lt p₁ hp
    exact WithBot.add_lt_add_left (mt degree_eq_bot.mp hq) this
  · refine ⟨p₁ / p₂, ?_⟩
    have h : p₂ * (p₁ / p₂) + p₁ % p₂ = p₁ := EuclideanDomain.div_add_mod p₁ p₂
    rw [← mul_sub, mul_assoc, sub_eq_iff_eq_add.mpr h.symm]
