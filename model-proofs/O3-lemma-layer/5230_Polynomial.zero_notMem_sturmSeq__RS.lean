/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     Polynomial.zero_notMem_sturmSeq
Source:      Mathlib @ a02a63c2, Mathlib/Algebra/Polynomial/Sturm/Sequence.lean, line 109
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  O3-lemma-layer, arm RS, verified in round 1 (round 0 = first attempt)
Prover:      claude-opus-5-5
Setup:       Opus 5.5 with repair loop: arm R = repair only; arm RS = repair plus the Lean-checked lemma layer
Check:       the proof replaced the human proof in the Mathlib file above; Lean reported
             0 errors and no `sorry`; sorry/admit/native_decide/search tactics were rejected.
-/

namespace Polynomial
variable {K : Type*} [Field K] [DecidableEq K]

lemma zero_notMem_sturmSeq (p q : K[X]) : 0 ∉ sturmSeq p q := by
  suffices H : ∀ n, ∀ p q : K[X], q.natDegree < n → 0 ∉ sturmSeq p q from
    H _ p q (Nat.lt_succ_self _)
  intro n
  induction n with
  | zero => intro p q h; omega
  | succ n ih =>
    intro p q hq
    by_cases hp : p = 0
    · subst hp; simp [sturmSeq_zero_left]
    rw [sturmSeq_cons hp]
    simp only [List.mem_cons, not_or]
    refine ⟨fun h => hp h.symm, ?_⟩
    by_cases hq0 : q = 0
    · subst hq0; simp [sturmSeq_zero_left]
    by_cases h0 : q.natDegree = 0
    · have hu : IsUnit q := Polynomial.isUnit_iff_degree_eq_zero.mpr
        (by simp [degree_eq_natDegree hq0, h0])
      have hm : -p % q = 0 := (EuclideanDomain.mod_eq_zero).mpr hu.dvd
      rw [hm, sturmSeq_zero_right, if_neg hq0]
      intro h
      rw [List.mem_singleton] at h
      exact hq0 h.symm
    · exact ih _ _ (lt_of_lt_of_le (Polynomial.natDegree_mod_lt (-p) h0) (by omega))
