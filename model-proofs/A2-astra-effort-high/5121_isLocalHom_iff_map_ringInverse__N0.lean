/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     isLocalHom_iff_map_ringInverse
Source:      Mathlib @ a02a63c2, Mathlib/Algebra/GroupWithZero/Units/Lemmas.lean, line 44
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  A2-astra-effort-high, arm N0, verified in round 0 (round 0 = first attempt)
Prover:      gpt-6-astra
Setup:       GPT-6 Astra, reasoning effort high (arms R, N0)
Check:       the proof replaced the human proof in the Mathlib file above; Lean reported
             0 errors and no `sorry`; sorry/admit/native_decide/search tactics were rejected.
-/

open scoped Ring
variable {M M₀ G₀ M₀' G₀' F F' : Type*}
variable [MonoidWithZero M₀]
section MonoidWithZero
variable [MonoidWithZero M₀'] [FunLike F M₀ M₀']

theorem isLocalHom_iff_map_ringInverse [MonoidWithZeroHomClass F M₀ M₀'] [Nontrivial M₀'] (f : F) :
    IsLocalHom f ↔ ∀ a, f a⁻¹ʳ = (f a)⁻¹ʳ := by
  classical
  constructor
  · intro hf
    letI : IsLocalHom f := hf
    intro a
    exact map_ringInverse f a
  · intro hf
    constructor
    intro a ha
    by_contra hna
    have h := hf a
    change f (if h : IsUnit a then ↑h.unit⁻¹ else 0) =
      (if h : IsUnit (f a) then ↑h.unit⁻¹ else 0) at h
    rw [dif_neg hna, dif_pos ha, map_zero] at h
    exact (Units.ne_zero (ha.unit⁻¹)) h.symm
