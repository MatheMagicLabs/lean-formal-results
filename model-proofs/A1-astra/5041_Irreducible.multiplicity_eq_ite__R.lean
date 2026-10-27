/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     Irreducible.multiplicity_eq_ite
Source:      Mathlib @ a02a63c2, Mathlib/RingTheory/Multiplicity.lean, line 516
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  A1-astra, arm R, verified in round 1 (round 0 = first attempt)
Prover:      gpt-6-astra
Setup:       GPT-6 Astra (Codex, effort medium): R = proof plus up to 3 repair rounds with Lean errors; RS = R plus lemma layer; RT = R with read-only Mathlib sources to search; N0-N3 = independent attempts
Check:       the proof replaced the human proof in the Mathlib file above; Lean reported
             0 errors and no `sorry`; sorry/admit/native_decide/search tactics were rejected.
-/

variable {α β : Type*}
open Nat
open scoped Classical in
section Monoid
variable [Monoid α] [Monoid β] {a b : α}
end Monoid
section CommMonoid
variable [CommMonoid α]

theorem Irreducible.multiplicity_eq_ite (p : α) {q : α} [Decidable (Associated p q)]
    (hq : Irreducible q) : multiplicity p q = if Associated p q then 1 else 0 := by
  by_cases h : Associated p q
  · rw [if_pos h]
    have hp : ¬ IsUnit p := fun hp => hq.not_isUnit (h.isUnit_iff.mp hp)
    apply multiplicity_eq_of_dvd_of_not_dvd
    · simpa using h.dvd
    · rintro ⟨c, hc⟩
      have hc' : q = p * (p * c) := by
        simpa [pow_succ, mul_assoc] using hc
      rcases hq.isUnit_or_isUnit hc' with hu | hu
      · exact hp hu
      · exact hp (isUnit_of_mul_isUnit_left hu)
  · rw [if_neg h]
    by_cases hp : IsUnit p
    · first
      | exact multiplicity_eq_zero_of_isUnit hp
      | exact multiplicity_of_isUnit_left hp
      | exact multiplicity_of_isUnit_left hp q
      | simp [multiplicity, hp]
    · apply multiplicity_eq_zero_of_not_dvd
      rintro ⟨c, hc⟩
      rcases hq.isUnit_or_isUnit hc with hu | hu
      · exact hp hu
      · rcases hu with ⟨u, hu⟩
        apply h
        exact ⟨u, by simpa [hu] using hc.symm⟩
