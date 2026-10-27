/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     Polynomial.sturmSeq_mul_left
Source:      Mathlib @ a02a63c2, Mathlib/Algebra/Polynomial/Sturm/Sequence.lean, line 139
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  O3-lemma-layer, arm RS, verified in round 1 (round 0 = first attempt)
Prover:      claude-opus-5-5
Setup:       Opus 5.5 with repair loop: arm R = repair only; arm RS = repair plus the Lean-checked lemma layer
Check:       the proof replaced the human proof in the Mathlib file above; Lean reported
             0 errors and no `sorry`; sorry/admit/native_decide/search tactics were rejected.
-/

namespace Polynomial
variable {K : Type*} [Field K] [DecidableEq K]

lemma sturmSeq_mul_left {r : K[X]} (hr : r ≠ 0) (p q : K[X]) :
    sturmSeq (r * p) (r * q) = (sturmSeq p q).map (r * ·) := by
  have h0 : ∀ p : K[X], sturmSeq (r * p) (r * 0) = (sturmSeq p 0).map (r * ·) := by
    intro p
    rw [mul_zero, sturmSeq_zero_right, sturmSeq_zero_right]
    by_cases hp : p = 0 <;> simp [hp, hr]
  have h : ∀ n : ℕ, ∀ p q : K[X], (q = 0 ∨ q.natDegree < n) →
      sturmSeq (r * p) (r * q) = (sturmSeq p q).map (r * ·) := by
    intro n
    induction n with
    | zero =>
      intro p q hq
      rcases hq with rfl | h
      · exact h0 p
      · exact absurd h (Nat.not_lt_zero _)
    | succ n ih =>
      intro p q hq
      by_cases hq0 : q = 0
      · subst hq0; exact h0 p
      by_cases hp : p = 0
      · subst hp; simp [sturmSeq_zero_left]
      have hlt : q.natDegree < n + 1 := by
        rcases hq with h | h
        · exact absurd h hq0
        · exact h
      rw [sturmSeq_cons (mul_ne_zero hr hp), sturmSeq_cons hp, ← mul_neg,
        mul_mod_mul_left]
      have key : (-p % q = 0 ∨ (-p % q).natDegree < n) := by
        by_cases hm : -p % q = 0
        · exact Or.inl hm
        · right
          have := natDegree_lt_natDegree hm (degree_mod_lt (-p) hq0)
          omega
      rw [ih q (-p % q) key]
      simp
  exact h (q.natDegree + 1) p q (Or.inr (Nat.lt_succ_self _))
