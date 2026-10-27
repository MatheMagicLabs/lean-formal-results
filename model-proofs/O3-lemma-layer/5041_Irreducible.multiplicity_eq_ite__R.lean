/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     Irreducible.multiplicity_eq_ite
Source:      Mathlib @ a02a63c2, Mathlib/RingTheory/Multiplicity.lean, line 516
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  O3-lemma-layer, arm R, verified in round 2 (round 0 = first attempt)
Prover:      claude-opus-5-5
Setup:       Opus 5.5 with repair loop: arm R = repair only; arm RS = repair plus the Lean-checked lemma layer
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
  · apply multiplicity_eq_of_emultiplicity_eq_some
    rw [emultiplicity_eq_coe]
    refine ⟨by simpa using h.dvd, ?_⟩
    rw [(h.pow_pow (n := 1 + 1)).dvd_iff_dvd_left]
    rintro ⟨c, hc⟩
    rw [pow_succ, pow_one, mul_assoc] at hc
    rcases hq.isUnit_or_isUnit hc with hu | hu
    · exact hq.1 hu
    · exact hq.1 (isUnit_of_mul_isUnit_left hu)
  · by_cases hp : IsUnit p
    · obtain ⟨u, rfl⟩ := hp
      first
        | simp [multiplicity, emultiplicity_unit_left]
        | exact multiplicity_unit_left _ _
        | simp [multiplicity_unit_left]
        | (rw [multiplicity, emultiplicity_unit_left]; rfl)
        | simp [multiplicity, emultiplicity]
    · have he : emultiplicity p q = 0 := by
        rw [emultiplicity_eq_zero]
        rintro ⟨c, hc⟩
        rcases hq.isUnit_or_isUnit hc with hu | hu
        · exact hp hu
        · exact h ⟨hu.unit, hc.symm⟩
      exact multiplicity_eq_of_emultiplicity_eq_some (by exact_mod_cast he)
