/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     HasUniqueRoots.mk'
Source:      Mathlib @ a02a63c2, Mathlib/Algebra/GroupWithZero/Torsion.lean, line 26
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  E1-repair-decomposition, arm V, verified in round 1 (round 0 = first attempt)
Prover:      gpt-6-astra
Setup:       GPT-6 Astra, which part of Lean feedback makes repair work: after a shared first attempt (E0), V = full error messages, Z = line numbers only, B = only "Lean rejected this proof"
Check:       the proof replaced the human proof in the Mathlib file above; Lean reported
             0 errors and no `sorry`; sorry/admit/native_decide/search tactics were rejected.
-/

variable {M : Type*} [CommMonoidWithZero M]

theorem HasUniqueRoots.mk' [IsReduced M]
    (ih : ∀ x ≠ 0, ∀ y ≠ 0, ∀ n ≠ 0, (x ^ n : M) = y ^ n → x = y) :
    HasUniqueRoots M := by
  have aux : ∀ (n : ℕ), n ≠ 0 → ∀ (x y : M),
      x ^ n = y ^ n → x = y := by
    intro n hn x y h
    by_cases hx : x = 0
    · subst x
      have hy : IsNilpotent y := ⟨n, by simpa [zero_pow hn] using h.symm⟩
      exact hy.eq_zero.symm
    · by_cases hy : y = 0
      · subst y
        have hx' : IsNilpotent x := ⟨n, by simpa [zero_pow hn] using h⟩
        exact hx'.eq_zero
      · exact ih x hx y hy n hn h
  constructor
  intros
  apply aux <;> assumption
