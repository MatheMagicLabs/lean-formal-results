/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     Ideal.depth_eq_sSup_length_isRegular
Source:      Mathlib @ a02a63c2, Mathlib/RingTheory/Depth/Basic.lean, line 337
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  O5-repair-sonnet, arm A, attempt 3, verified in round 0 (round 0 = first attempt)
Prover:      claude-sonnet-5-5
Setup:       Sonnet 5.5: arm B = repair loop; arm A = independent attempts
Check:       the proof replaced the human proof in the Mathlib file above; Lean reported
             0 errors and no `sorry`; sorry/admit/native_decide/search tactics were rejected.
-/

-- (context: the Mathlib file above this declaration)
lemma Ideal.depth_eq_sSup_length_isRegular [IsNoetherianRing R] (I : Ideal R)
    (M : ModuleCat.{v} R) [Module.Finite R M] (smul_lt : I • (⊤ : Submodule R M) < ⊤) :
    I.depth M = sSup {(List.length rs : ℕ∞) | (rs : List R)
      (_ : IsRegular M rs) (_ : ∀ r ∈ rs, r ∈ I)} := by
  have hI : I ≠ ⊤ := by
    rintro rfl
    simp at smul_lt
  haveI : Nontrivial (R ⧸ I) := Ideal.Quotient.nontrivial_iff.mpr hI
  haveI : Nontrivial (Shrink.{v} (R ⧸ I)) := (equivShrink (R ⧸ I)).symm.nontrivial
  haveI : Module.Finite R (Shrink.{v} (R ⧸ I)) :=
    Module.Finite.equiv (Shrink.linearEquiv R (R ⧸ I)).symm
  have hann : Module.annihilator R (R ⧸ I) = I := by
    ext x
    rw [Module.mem_annihilator]
    constructor
    · intro h
      have := h 1
      rw [Algebra.smul_def, mul_one] at this
      exact (Ideal.Quotient.eq_zero_iff_mem).mp this
    · intro hx m
      obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective m
      show Ideal.Quotient.mk I x * Ideal.Quotient.mk I y = 0
      rw [← map_mul]
      exact Ideal.Quotient.eq_zero_iff_mem.mpr (I.mul_mem_right _ hx)
  refine ModuleCat.depth_eq_sSup_length_isRegular I ↧(Shrink.{v} (R ⧸ I)) M smul_lt ?_
  rw [Module.support_eq_zeroLocus, (Shrink.linearEquiv R (R ⧸ I)).annihilator_eq, hann]
