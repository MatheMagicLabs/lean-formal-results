/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     Ideal.depth_eq_sSup_length_isRegular
Source:      Mathlib @ a02a63c2, Mathlib/RingTheory/Depth/Basic.lean, line 337
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  O5-repair-sonnet, arm B, verified in round 2 (round 0 = first attempt)
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
    refine smul_lt.ne ?_
    rw [eq_top_iff]
    intro x _
    have := Submodule.smul_mem_smul (Submodule.mem_top : (1 : R) ∈ (⊤ : Ideal R))
      (Submodule.mem_top : x ∈ (⊤ : Submodule R M))
    rwa [one_smul] at this
  haveI : Nontrivial (R ⧸ I) := Ideal.Quotient.nontrivial_iff.mpr hI
  let e : Shrink.{v} (R ⧸ I) ≃ₗ[R] (R ⧸ I) := Shrink.linearEquiv R (R ⧸ I)
  haveI : Module.Finite R (Shrink.{v} (R ⧸ I)) := Module.Finite.equiv e.symm
  haveI : Nontrivial (Shrink.{v} (R ⧸ I)) := e.toEquiv.nontrivial
  have hann : Module.annihilator R (R ⧸ I) = I := by
    ext r
    rw [Module.mem_annihilator]
    constructor
    · intro h
      have h1 := h 1
      rw [Algebra.smul_def, mul_one] at h1
      have h2 : Ideal.Quotient.mk I r = 0 := h1
      exact Ideal.Quotient.eq_zero_iff_mem.mp h2
    · intro hr q
      obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective q
      have h0 : Ideal.Quotient.mk I r = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr hr
      rw [Algebra.smul_def]
      show Ideal.Quotient.mk I r * Ideal.Quotient.mk I a = 0
      rw [h0, zero_mul]
  have hsupp : Module.support R (Shrink.{v} (R ⧸ I)) = PrimeSpectrum.zeroLocus I := by
    rw [LinearEquiv.support_eq e]
    first
      | (rw [Module.support_eq_zeroLocus, hann])
      | (rw [Module.support_eq_zeroLocus]; simp [hann])
      | simp [Module.support_eq_zeroLocus, hann]
  exact ModuleCat.depth_eq_sSup_length_isRegular I (↧(Shrink.{v} (R ⧸ I))) M smul_lt hsupp
