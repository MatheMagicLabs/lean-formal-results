/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     HasUniqueRoots.mk'
Source:      Mathlib @ a02a63c2, Mathlib/Algebra/GroupWithZero/Torsion.lean, line 26
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  O3LA3-leanstral-agent-feedback, arm rueck, verified in final
Prover:      labs-leanstral-1-5
Setup:       Leanstral 1.5 agent with goal-state feedback (arm rueck)
Check:       the proof replaced the human proof in the Mathlib file above; Lean reported
             0 errors and no `sorry`; sorry/admit/native_decide/search tactics were rejected.
-/

variable {M : Type*} [CommMonoidWithZero M]

theorem HasUniqueRoots.mk' [IsReduced M]
    (ih : ∀ x ≠ 0, ∀ y ≠ 0, ∀ n ≠ 0, (x ^ n : M) = y ^ n → x = y) :
    HasUniqueRoots M := by
  refine { pow_left_injective := ?_ }
  intro n hn
  intro a b h
  have h' : a ^ n = b ^ n := h
  by_cases ha : a = 0
  · subst ha
    rw [zero_pow hn] at h'
    have hb : b = 0 := eq_zero_of_pow_eq_zero h'.symm
    subst hb
    rfl
  · by_cases hb : b = 0
    · subst hb
      rw [zero_pow hn] at h'
      have ha' : a = 0 := eq_zero_of_pow_eq_zero h'
      exact (ha ha').elim
    · exact ih a ha b hb n hn h'
