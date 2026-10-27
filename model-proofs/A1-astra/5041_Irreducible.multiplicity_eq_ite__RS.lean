/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     Irreducible.multiplicity_eq_ite
Source:      Mathlib @ a02a63c2, Mathlib/RingTheory/Multiplicity.lean, line 516
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  A1-astra, arm RS, verified in round 1 (round 0 = first attempt)
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
  split_ifs with h
  · rw [← multiplicity_eq_of_associated_left h]
    exact hq.multiplicity_self
  · by_cases hp : IsUnit p
    · exact multiplicity_of_isUnit_left hp q
    · apply multiplicity_eq_zero_of_not_dvd
      rintro ⟨r, hr⟩
      rcases (irreducible_iff.mp hq).2 hr with hp' | hr'
      · exact hp hp'
      · rcases hr' with ⟨u, hu⟩
        apply h
        exact ⟨u, by simpa only [hu] using hr.symm⟩
