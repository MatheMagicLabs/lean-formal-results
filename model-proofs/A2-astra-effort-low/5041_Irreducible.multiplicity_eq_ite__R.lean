/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     Irreducible.multiplicity_eq_ite
Source:      Mathlib @ a02a63c2, Mathlib/RingTheory/Multiplicity.lean, line 516
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  A2-astra-effort-low, arm R, verified in round 1 (round 0 = first attempt)
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
  classical
  have unit_case (hp : IsUnit p) : multiplicity p q = 0 := by
    first
    | simpa using hp.multiplicity_eq_zero q
    | simpa using multiplicity_eq_zero_of_isUnit hp q
    | simp [multiplicity, hp]
  have one_case (h : Associated p q) : multiplicity p q = 1 := by
    rcases h with ⟨u, hu⟩
    have hp : ¬ IsUnit p := by
      intro hp
      apply hq.not_isUnit
      rw [← hu]
      exact hp.mul u.isUnit
    have hd : p ^ 1 ∣ q := by
      simpa using (show p ∣ q from ⟨↑u, hu.symm⟩)
    have hn : ¬ p ^ (1 + 1) ∣ q := by
      rintro ⟨r, hr⟩
      have he : q = p * (p * r) := by
        simpa [pow_succ, mul_assoc] using hr
      have hf : IsUnit p ∨ IsUnit (p * r) := by
        first
        | exact hq.isUnit_or_isUnit he
        | exact hq.isUnit_or_isUnit he.symm
        | exact hq.isUnit_or_isUnit p (p * r) he
        | exact hq.isUnit_or_isUnit p (p * r) he.symm
      rcases hf with hf | hf
      · exact hp hf
      · exact hp (isUnit_of_mul_isUnit_left hf)
    exact multiplicity_eq_of_dvd_of_not_dvd hd hn
  split_ifs with h
  · exact one_case h
  · by_cases hp : IsUnit p
    · exact unit_case hp
    · have hn : ¬ p ∣ q := by
        rintro ⟨r, hr⟩
        have hf : IsUnit p ∨ IsUnit r := by
          first
          | exact hq.isUnit_or_isUnit hr
          | exact hq.isUnit_or_isUnit hr.symm
          | exact hq.isUnit_or_isUnit p r hr
          | exact hq.isUnit_or_isUnit p r hr.symm
        rcases hf with hf | ⟨u, hu⟩
        · exact hp hf
        · apply h
          exact ⟨u, by simpa [hu] using hr.symm⟩
      first
      | exact multiplicity_eq_zero_of_not_dvd hn
      | exact multiplicity_eq_of_dvd_of_not_dvd
          (by simp : p ^ 0 ∣ q) (by simpa using hn)
