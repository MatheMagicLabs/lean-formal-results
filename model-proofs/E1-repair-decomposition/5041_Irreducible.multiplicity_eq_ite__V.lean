/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     Irreducible.multiplicity_eq_ite
Source:      Mathlib @ a02a63c2, Mathlib/RingTheory/Multiplicity.lean, line 516
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  E1-repair-decomposition, arm V, verified in round 1 (round 0 = first attempt)
Prover:      gpt-6-astra
Setup:       GPT-6 Astra, which part of Lean feedback makes repair work: after a shared first attempt (E0), V = full error messages, Z = line numbers only, B = only "Lean rejected this proof"
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
  classical
  by_cases h : Associated p q
  · rw [if_pos h]
    first
    | simpa only [multiplicity_eq_of_associated h] using hq.multiplicity_self
    | simpa only [multiplicity_eq_of_associated_left h] using hq.multiplicity_self
    | simpa only [h.multiplicity_eq] using hq.multiplicity_self
    | have hp : ¬ IsUnit p := fun hp =>
        hq.not_isUnit (h.isUnit_iff.mp hp)
      have hd : p ∣ q := h.dvd
      have hn : ¬ p ^ 2 ∣ q := by
        rintro ⟨r, hr⟩
        have he : q = p * (p * r) := by
          simpa only [pow_two, mul_assoc] using hr
        rcases hq.isUnit_or_isUnit he with hu | hu
        · exact hp hu
        · exact hp (isUnit_mul_iff.mp hu).1
      first
      | exact multiplicity_eq_one_of_dvd_of_not_dvd hd hn
      | apply multiplicity_eq_of_dvd_of_not_dvd
        · simpa using hd
        · simpa using hn
  · rw [if_neg h]
    by_cases hp : IsUnit p
    · simp [multiplicity, hp]
    · apply multiplicity_eq_zero_of_not_dvd
      rintro ⟨r, hr⟩
      rcases hq.isUnit_or_isUnit hr with hu | hu
      · exact hp hu
      · apply h
        rcases hu with ⟨u, hu⟩
        exact ⟨u, by simpa only [hu] using hr.symm⟩
