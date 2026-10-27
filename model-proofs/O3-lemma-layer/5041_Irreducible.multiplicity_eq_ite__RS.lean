/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     Irreducible.multiplicity_eq_ite
Source:      Mathlib @ a02a63c2, Mathlib/RingTheory/Multiplicity.lean, line 516
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  O3-lemma-layer, arm RS, verified in round 1 (round 0 = first attempt)
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
  · have hp : Irreducible p := h.symm.irreducible hq
    apply multiplicity_eq_of_emultiplicity_eq_some
    rw [emultiplicity_eq_coe]
    refine ⟨by simpa using h.dvd, ?_⟩
    rintro ⟨c, hc⟩
    have hc' : q = p * (p * c) := by rw [hc, pow_succ, pow_one, mul_assoc]
    rcases hq.isUnit_or_isUnit hc' with h1 | h1
    · exact hp.not_isUnit h1
    · exact hp.not_isUnit (isUnit_of_mul_isUnit_left h1)
  · by_cases hd : p ∣ q
    · obtain ⟨c, hc⟩ := hd
      rcases hq.isUnit_or_isUnit hc with hu | hu
      · simp [multiplicity, emultiplicity, hu, hu.dvd]
      · exact absurd ⟨hu.unit, hc.symm⟩ h
    · apply multiplicity_eq_of_emultiplicity_eq_some
      simpa using emultiplicity_eq_zero.2 hd
