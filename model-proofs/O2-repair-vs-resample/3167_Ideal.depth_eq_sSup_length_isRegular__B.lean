/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     Ideal.depth_eq_sSup_length_isRegular
Source:      Mathlib @ a02a63c2, Mathlib/RingTheory/Depth/Basic.lean, line 337
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  O2-repair-vs-resample, arm B, verified in round 1 (round 0 = first attempt)
Prover:      claude-opus-5-5
Setup:       Opus 5.5: arm B = one attempt plus up to 3 repair rounds with Lean error messages; arm A = 4 independent attempts (attempt k)
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
  haveI : Nontrivial (R ⧸ I) := by
    refine ⟨⟨0, 1, fun h => hI ?_⟩⟩
    rw [Ideal.eq_top_iff_one, ← Ideal.Quotient.eq_zero_iff_mem, map_one]
    exact h.symm
  let e : Shrink.{v} (R ⧸ I) ≃ₗ[R] R ⧸ I := Shrink.linearEquiv R (R ⧸ I)
  haveI : Module.Finite R (Shrink.{v} (R ⧸ I)) := Module.Finite.equiv e.symm
  haveI : Nontrivial (Shrink.{v} (R ⧸ I)) := e.toEquiv.nontrivial
  have hsupp : Module.support R (Shrink.{v} (R ⧸ I)) = PrimeSpectrum.zeroLocus I := by
    rw [Module.support_eq_zeroLocus]
    congr 1
    ext r
    simp only [SetLike.mem_coe]
    rw [Module.mem_annihilator]
    constructor
    · intro h
      have h1 := congrArg e (h (e.symm 1))
      rw [map_smul, LinearEquiv.apply_symm_apply, map_zero, Algebra.smul_def, mul_one,
        Ideal.Quotient.algebraMap_eq, Ideal.Quotient.eq_zero_iff_mem] at h1
      exact h1
    · intro h m
      apply e.injective
      rw [map_smul, map_zero]
      obtain ⟨x, hx⟩ := Ideal.Quotient.mk_surjective (e m)
      rw [← hx, Algebra.smul_def, Ideal.Quotient.algebraMap_eq, ← map_mul,
        Ideal.Quotient.eq_zero_iff_mem]
      exact I.mul_mem_right x h
  rw [Ideal.depth]
  exact ModuleCat.depth_eq_sSup_length_isRegular I _ M smul_lt hsupp
