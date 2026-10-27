/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     Polynomial.sturmSeq_mul_left
Source:      Mathlib @ a02a63c2, Mathlib/Algebra/Polynomial/Sturm/Sequence.lean, line 139
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  O4-layer-with-search, arm RT, verified in round 0 (round 0 = first attempt)
Prover:      claude-opus-5-5
Setup:       Opus 5.5 with repair loop, lemma layer and name search (arm RT)
Check:       the proof replaced the human proof in the Mathlib file above; Lean reported
             0 errors and no `sorry`; sorry/admit/native_decide/search tactics were rejected.
-/

namespace Polynomial
variable {K : Type*} [Field K] [DecidableEq K]

lemma sturmSeq_mul_left {r : K[X]} (hr : r ≠ 0) (p q : K[X]) :
    sturmSeq (r * p) (r * q) = (sturmSeq p q).map (r * ·) := by
  suffices h : ∀ n : ℕ, ∀ p q : K[X], (if q = 0 then 0 else q.natDegree + 1) ≤ n →
      sturmSeq (r * p) (r * q) = (sturmSeq p q).map (r * ·) from h _ p q le_rfl
  intro n
  induction n with
  | zero =>
    intro p q hq
    have : q = 0 := by
      by_contra h0
      simp [h0] at hq
    subst this
    simp only [mul_zero, sturmSeq_zero_right, mul_eq_zero, hr, false_or]
    split_ifs <;> simp
  | succ n ih =>
    intro p q hq
    by_cases hq0 : q = 0
    · subst hq0
      simp only [mul_zero, sturmSeq_zero_right, mul_eq_zero, hr, false_or]
      split_ifs <;> simp
    by_cases hp0 : p = 0
    · subst hp0
      simp [sturmSeq_zero_left]
    simp only [if_neg hq0] at hq
    have hc : (if -p % q = 0 then 0 else (-p % q).natDegree + 1) ≤ n := by
      split_ifs with h
      · omega
      · have := natDegree_lt_natDegree h (degree_mod_lt (-p) hq0)
        omega
    rw [sturmSeq_cons (mul_ne_zero hr hp0), sturmSeq_cons hp0, ← mul_neg,
      mul_mod_mul_left, ih q (-p % q) hc, List.map_cons]
