/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     Polynomial.dvd_of_mem_sturmSeq
Source:      Mathlib @ a02a63c2, Mathlib/Algebra/Polynomial/Sturm/Sequence.lean, line 127
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  A1-astra, arm RS, verified in round 0 (round 0 = first attempt)
Prover:      gpt-6-astra
Setup:       GPT-6 Astra (Codex, effort medium): R = proof plus up to 3 repair rounds with Lean errors; RS = R plus lemma layer; RT = R with read-only Mathlib sources to search; N0-N3 = independent attempts
Check:       the proof replaced the human proof in the Mathlib file above; Lean reported
             0 errors and no `sorry`; sorry/admit/native_decide/search tactics were rejected.
-/

namespace Polynomial
variable {K : Type*} [Field K] [DecidableEq K]

lemma dvd_of_mem_sturmSeq {d p q s : K[X]} (hp : d ∣ p) (hq : d ∣ q)
    (hs : s ∈ sturmSeq p q) : d ∣ s := by
  have aux : ∀ (l : List K[X]) (p q : K[X]),
      sturmSeq p q = l → d ∣ p → d ∣ q → ∀ s ∈ l, d ∣ s := by
    intro l
    induction l with
    | nil =>
        intro p q he hp hq s hs
        simp at hs
    | cons a l ih =>
        intro p q he hp hq s hs
        have hp0 : p ≠ 0 := by
          intro h
          have hn : sturmSeq p q = [] := sturmSeq_eq_nil_iff.mpr h
          rw [hn] at he
          cases he
        rw [sturmSeq_cons hp0] at he
        obtain ⟨rfl, ht⟩ := List.cons.inj he
        rcases List.mem_cons.mp hs with rfl | hs
        · exact hp
        · have hr : d ∣ -p % q := by
            rw [eq_sub_of_add_eq (EuclideanDomain.mod_add_div (-p) q)]
            exact (dvd_neg.mpr hp).sub
              (dvd_mul_of_dvd_left hq ((-p) / q))
          exact ih q (-p % q) ht hq hr s hs
  exact aux (sturmSeq p q) p q rfl hp hq s hs
