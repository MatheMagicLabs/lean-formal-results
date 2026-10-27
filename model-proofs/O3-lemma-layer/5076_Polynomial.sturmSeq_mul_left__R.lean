/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     Polynomial.sturmSeq_mul_left
Source:      Mathlib @ a02a63c2, Mathlib/Algebra/Polynomial/Sturm/Sequence.lean, line 139
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  O3-lemma-layer, arm R, verified in round 2 (round 0 = first attempt)
Prover:      claude-opus-5-5
Setup:       Opus 5.5 with repair loop: arm R = repair only; arm RS = repair plus the Lean-checked lemma layer
Check:       the proof replaced the human proof in the Mathlib file above; Lean reported
             0 errors and no `sorry`; sorry/admit/native_decide/search tactics were rejected.
-/

namespace Polynomial
variable {K : Type*} [Field K] [DecidableEq K]

lemma sturmSeq_mul_left {r : K[X]} (hr : r ≠ 0) (p q : K[X]) :
    sturmSeq (r * p) (r * q) = (sturmSeq p q).map (r * ·) := by
  have key : ∀ a b : K[X], (r * a) % (r * b) = r * (a % b) := by
    intro a b
    by_cases hb : b = 0
    · subst hb; simp
    have hrb : r * b ≠ 0 := mul_ne_zero hr hb
    have h1 := EuclideanDomain.div_add_mod (r * a) (r * b)
    have h2 := EuclideanDomain.div_add_mod a b
    have e1 : (r * a) % (r * b) = r * a - r * b * ((r * a) / (r * b)) := by
      rw [eq_sub_iff_add_eq, add_comm]; exact h1
    have e2 : a % b = a - b * (a / b) := by
      rw [eq_sub_iff_add_eq, add_comm]; exact h2
    have hd : (r * b) ∣ ((r * a) % (r * b) - r * (a % b)) :=
      ⟨a / b - (r * a) / (r * b), by rw [e1, e2]; ring⟩
    have := Polynomial.eq_zero_of_dvd_of_degree_lt hd ?_
    · exact sub_eq_zero.mp this
    · refine lt_of_le_of_lt (degree_sub_le _ _) (max_lt ?_ ?_)
      · exact EuclideanDomain.mod_lt _ hrb
      · rw [degree_mul, degree_mul]
        exact WithBot.add_lt_add_left (degree_ne_bot.mpr hr) (EuclideanDomain.mod_lt a hb)
  induction p, q using sturmSeq.induct
  all_goals
    conv_lhs => rw [sturmSeq]
    conv_rhs => rw [sturmSeq]
    simp_all [key]
  all_goals
    rw [← mul_neg, key]
    assumption
