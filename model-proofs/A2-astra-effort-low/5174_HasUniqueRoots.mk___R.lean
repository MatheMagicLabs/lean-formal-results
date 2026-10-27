/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     HasUniqueRoots.mk'
Source:      Mathlib @ a02a63c2, Mathlib/Algebra/GroupWithZero/Torsion.lean, line 26
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  A2-astra-effort-low, arm R, verified in round 1 (round 0 = first attempt)
Prover:      gpt-6-astra
Setup:       GPT-6 Astra, reasoning effort low (arms R, N0)
Check:       the proof replaced the human proof in the Mathlib file above; Lean reported
             0 errors and no `sorry`; sorry/admit/native_decide/search tactics were rejected.
-/

variable {M : Type*} [CommMonoidWithZero M]

theorem HasUniqueRoots.mk' [IsReduced M]
    (ih : ∀ x ≠ 0, ∀ y ≠ 0, ∀ n ≠ 0, (x ^ n : M) = y ^ n → x = y) :
    HasUniqueRoots M := by
  constructor
  intro n hn x y h
  by_cases hx : x = 0
  · have hy : IsNilpotent y :=
      ⟨n, by simpa [hx, hn] using h.symm⟩
    exact hx.trans hy.eq_zero.symm
  · by_cases hy : y = 0
    · have hx' : IsNilpotent x :=
        ⟨n, by simpa [hy, hn] using h⟩
      exact hx'.eq_zero.trans hy.symm
    · exact ih x hx y hy n hn h
