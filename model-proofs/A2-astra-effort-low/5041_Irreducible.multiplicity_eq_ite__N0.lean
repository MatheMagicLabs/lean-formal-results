/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     Irreducible.multiplicity_eq_ite
Source:      Mathlib @ a02a63c2, Mathlib/RingTheory/Multiplicity.lean, line 516
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  A2-astra-effort-low, arm N0, verified in round 0 (round 0 = first attempt)
Prover:      gpt-6-astra
Setup:       GPT-6 Astra, reasoning effort low (arms R, N0)
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
  by_cases hp : IsUnit p
  · have h : ¬ Associated p q := by
      intro h
      exact hq.not_isUnit (h.isUnit_iff.mp hp)
    rw [if_neg h]
    first
    | exact multiplicity_eq_zero_of_isUnit hp
    | exact hp.multiplicity_eq_zero
    | simp [multiplicity, hp]
  · have hsq : ¬ p ^ 2 ∣ q := by
      rintro ⟨c, hc⟩
      have hc' : q = p * (p * c) := by
        simpa [pow_two, mul_assoc] using hc
      rcases hq.isUnit_or_isUnit hc' with h | h
      · exact hp h
      · exact hp (isUnit_of_mul_isUnit_left h)
    by_cases h : Associated p q
    · rw [if_pos h]
      apply multiplicity_eq_of_dvd_of_not_dvd
      · simpa using h.dvd
      · simpa using hsq
    · rw [if_neg h]
      have hd : ¬ p ∣ q := by
        rintro ⟨c, hc⟩
        rcases hq.isUnit_or_isUnit hc with hu | hu
        · exact hp hu
        · rcases hu with ⟨u, rfl⟩
          exact h ⟨u, hc.symm⟩
      exact multiplicity_eq_zero_of_not_dvd hd
