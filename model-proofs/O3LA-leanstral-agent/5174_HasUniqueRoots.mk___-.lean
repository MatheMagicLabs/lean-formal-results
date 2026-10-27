/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     HasUniqueRoots.mk'
Source:      Mathlib @ a02a63c2, Mathlib/Algebra/GroupWithZero/Torsion.lean, line 26
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  O3LA-leanstral-agent, arm -, verified in final
Prover:      labs-leanstral-1-5
Setup:       Leanstral 1.5 as a tool-using agent (Mistral Vibe)
Check:       the proof replaced the human proof in the Mathlib file above; Lean reported
             0 errors and no `sorry`; sorry/admit/native_decide/search tactics were rejected.
-/

variable {M : Type*} [CommMonoidWithZero M]

theorem HasUniqueRoots.mk' [IsReduced M]
    (ih : ∀ x ≠ 0, ∀ y ≠ 0, ∀ n ≠ 0, (x ^ n : M) = y ^ n → x = y) :
    HasUniqueRoots M := by
  refine ⟨fun {n} hn {a b} h => ?_⟩
  dsimp at h
  by_cases ha : a = 0
  · rw [ha] at h
    have hb0 : b ^ n = 0 := by
      rw [zero_pow hn] at h
      exact h.symm
    have hb : b = 0 := ((pow_eq_zero_iff hn).mp hb0)
    rw [ha, hb]
  · by_cases hb : b = 0
    · rw [hb] at h
      have ha0 : a ^ n = 0 := by
        rw [zero_pow hn] at h
        exact h
      have ha' : a = 0 := ((pow_eq_zero_iff hn).mp ha0)
      contradiction
    · exact ih a ha b hb n hn h
