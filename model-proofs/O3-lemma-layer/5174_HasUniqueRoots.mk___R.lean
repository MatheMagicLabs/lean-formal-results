/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     HasUniqueRoots.mk'
Source:      Mathlib @ a02a63c2, Mathlib/Algebra/GroupWithZero/Torsion.lean, line 26
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  O3-lemma-layer, arm R, verified in round 0 (round 0 = first attempt)
Prover:      claude-opus-5-5
Setup:       Opus 5.5 with repair loop: arm R = repair only; arm RS = repair plus the Lean-checked lemma layer
Check:       the proof replaced the human proof in the Mathlib file above; Lean reported
             0 errors and no `sorry`; sorry/admit/native_decide/search tactics were rejected.
-/

variable {M : Type*} [CommMonoidWithZero M]

theorem HasUniqueRoots.mk' [IsReduced M]
    (ih : ∀ x ≠ 0, ∀ y ≠ 0, ∀ n ≠ 0, (x ^ n : M) = y ^ n → x = y) :
    HasUniqueRoots M := by
  constructor
  intro n hn x y hxy
  have hxy : x ^ n = y ^ n := hxy
  by_cases hx : x = 0
  · subst hx
    rw [zero_pow hn] at hxy
    exact (IsReduced.eq_zero y ⟨n, hxy.symm⟩).symm
  by_cases hy : y = 0
  · subst hy
    rw [zero_pow hn] at hxy
    exact IsReduced.eq_zero x ⟨n, hxy⟩
  exact ih x hx y hy n hn hxy
