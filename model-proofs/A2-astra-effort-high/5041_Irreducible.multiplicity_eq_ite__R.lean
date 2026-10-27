/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     Irreducible.multiplicity_eq_ite
Source:      Mathlib @ a02a63c2, Mathlib/RingTheory/Multiplicity.lean, line 516
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  A2-astra-effort-high, arm R, verified in round 1 (round 0 = first attempt)
Prover:      gpt-6-astra
Setup:       GPT-6 Astra, reasoning effort high (arms R, N0)
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
  · have hnot : ¬ Associated p q := by
      intro h
      exact hq.not_isUnit (h.isUnit_iff.mp hp)
    have hfin : ¬ FiniteMultiplicity p q := by
      rintro ⟨n, hn⟩
      exact hn ((hp.pow _).dvd)
    simp [hnot, multiplicity, hfin]
  · have hassoc : p ∣ q → Associated p q := by
      rintro ⟨r, hr⟩
      rcases hq.isUnit_or_isUnit hr with h | h
      · exact (hp h).elim
      · rcases h with ⟨u, hu⟩
        exact ⟨u, by simpa only [hu] using hr.symm⟩
    have hsq : ¬ p ^ (1 + 1) ∣ q := by
      rintro ⟨r, hr⟩
      have hr' : q = p * (p * r) := by
        simpa [pow_succ, mul_assoc] using hr
      rcases hq.isUnit_or_isUnit hr' with h | h
      · exact hp h
      · exact hp (isUnit_of_mul_isUnit_left h)
    by_cases h : Associated p q
    · rw [if_pos h]
      exact multiplicity_eq_of_dvd_of_not_dvd
        (by simpa using h.dvd) hsq
    · rw [if_neg h]
      apply multiplicity_eq_of_dvd_of_not_dvd
      · simp
      · simpa using
          (show ¬ p ∣ q from fun hd => h (hassoc hd))
