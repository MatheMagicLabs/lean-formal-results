/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     map_inv_eq_ringInverse_map
Source:      Mathlib @ a02a63c2, Mathlib/Algebra/GroupWithZero/Units/Lemmas.lean, line 72
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  A1-astra, arm R, verified in round 1 (round 0 = first attempt)
Prover:      gpt-6-astra
Setup:       GPT-6 Astra (Codex, effort medium): R = proof plus up to 3 repair rounds with Lean errors; RS = R plus lemma layer; RT = R with read-only Mathlib sources to search; N0-N3 = independent attempts
Check:       the proof replaced the human proof in the Mathlib file above; Lean reported
             0 errors and no `sorry`; sorry/admit/native_decide/search tactics were rejected.
-/

open scoped Ring
variable {M M₀ G₀ M₀' G₀' F F' : Type*}
variable [MonoidWithZero M₀]
section MonoidWithZero
variable [MonoidWithZero M₀'] [FunLike F M₀ M₀']
end MonoidWithZero
section Monoid
variable [Monoid M] [GroupWithZero G₀]

theorem map_inv_eq_ringInverse_map [FunLike F G₀ M₀]
    [MonoidWithZeroHomClass F G₀ M₀] (f : F) (a : G₀) :
    f a⁻¹ = (f a)⁻¹ʳ := by
  classical
  by_cases ha : a = 0
  · simp [ha]
  · let u : M₀ˣ :=
      { val := f a
        inv := f a⁻¹
        val_inv := by rw [← map_mul, mul_inv_cancel₀ ha, map_one]
        inv_val := by rw [← map_mul, inv_mul_cancel₀ ha, map_one] }
    change (↑(u⁻¹) : M₀) = (↑u)⁻¹ʳ
    unfold Ring.inverse
    split_ifs with h
    · change (↑(u⁻¹) : M₀) = ↑(h.unit⁻¹)
      have hu : h.unit = u := Units.ext h.unit_spec
      rw [hu]
    · exact (h u.isUnit).elim
