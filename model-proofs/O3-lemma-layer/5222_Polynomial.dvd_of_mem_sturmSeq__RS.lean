/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     Polynomial.dvd_of_mem_sturmSeq
Source:      Mathlib @ a02a63c2, Mathlib/Algebra/Polynomial/Sturm/Sequence.lean, line 127
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  O3-lemma-layer, arm RS, verified in round 0 (round 0 = first attempt)
Prover:      claude-opus-5-5
Setup:       Opus 5.5 with repair loop: arm R = repair only; arm RS = repair plus the Lean-checked lemma layer
Check:       the proof replaced the human proof in the Mathlib file above; Lean reported
             0 errors and no `sorry`; sorry/admit/native_decide/search tactics were rejected.
-/

namespace Polynomial
variable {K : Type*} [Field K] [DecidableEq K]

lemma dvd_of_mem_sturmSeq {d p q s : K[X]} (hp : d ∣ p) (hq : d ∣ q)
    (hs : s ∈ sturmSeq p q) : d ∣ s := by
  obtain ⟨n, hn⟩ : ∃ n, (sturmSeq p q).length ≤ n := ⟨_, le_rfl⟩
  induction n generalizing p q with
  | zero =>
    have := List.length_pos_of_mem hs
    omega
  | succ n ih =>
    by_cases hp0 : p = 0
    · subst hp0
      rw [sturmSeq_eq_nil_iff.mpr rfl] at hs
      simp at hs
    · rw [sturmSeq_cons hp0] at hs hn
      simp only [List.mem_cons] at hs
      rcases hs with rfl | hs
      · exact hp
      · have hmod : d ∣ -p % q := by
          have h := EuclideanDomain.div_add_mod (-p) q
          exact (dvd_add_right (dvd_mul_of_dvd_left hq _)).mp
            (by rw [h]; exact dvd_neg.mpr hp)
        exact ih hq hmod hs (by simp at hn; omega)
