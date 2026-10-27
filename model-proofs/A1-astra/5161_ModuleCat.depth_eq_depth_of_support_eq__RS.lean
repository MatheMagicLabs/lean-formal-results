/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     ModuleCat.depth_eq_depth_of_support_eq
Source:      Mathlib @ a02a63c2, Mathlib/RingTheory/Depth/Basic.lean, line 157
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  A1-astra, arm RS, verified in round 3 (round 0 = first attempt)
Prover:      gpt-6-astra
Setup:       GPT-6 Astra (Codex, effort medium): R = proof plus up to 3 repair rounds with Lean errors; RS = R plus lemma layer; RT = R with read-only Mathlib sources to search; N0-N3 = independent attempts
Check:       the proof replaced the human proof in the Mathlib file above; Lean reported
             0 errors and no `sorry`; sorry/admit/native_decide/search tactics were rejected.
-/

open IsLocalRing LinearMap Module
universe v u
open RingTheory.Sequence Ideal CategoryTheory Abelian Limits Pointwise ModuleCat IsSMulRegular
variable {R : Type u} [CommRing R] [Small.{v} R]
section depth
namespace ModuleCat
open Classical in

lemma depth_eq_depth_of_support_eq [IsNoetherianRing R] (I : Ideal R)
    (N M : ModuleCat.{v} R) [Module.Finite R M] [Module.Finite R N]
    [Nontrivial N] (smul_lt : I • (⊤ : Submodule R M) < ⊤)
    (hsupp : Module.support R N = PrimeSpectrum.zeroLocus I) :
    N.depth M = I.depth M := by
  let P : ModuleCat.{v} R := ModuleCat.of R (Shrink.{v} (R ⧸ I))
  have hP : Module.support R P = PrimeSpectrum.zeroLocus I := by
    let e : (R ⧸ I) ≃ₗ[R] Shrink.{v} (R ⧸ I) :=
      (Shrink.linearEquiv R (R ⧸ I)).symm
    have hann :
        Module.annihilator R (Shrink.{v} (R ⧸ I)) =
          Module.annihilator R (R ⧸ I) := by
      ext r
      rw [Module.mem_annihilator, Module.mem_annihilator]
      constructor
      · intro h x
        apply e.injective
        simpa only [map_smul, map_zero] using h (e x)
      · intro h x
        obtain ⟨y, rfl⟩ := e.surjective x
        simpa only [map_smul, map_zero] using congrArg e (h y)
    have hquot : Module.annihilator R (R ⧸ I) = I := by
      ext r
      rw [Module.mem_annihilator]
      constructor
      · intro h
        have hr := h (1 : R ⧸ I)
        change Ideal.Quotient.mk I r * 1 = 0 at hr
        exact Ideal.Quotient.eq_zero_iff_mem.mp (by
          simpa only [mul_one] using hr)
      · intro hr x
        have hr' : Ideal.Quotient.mk I r = 0 :=
          Ideal.Quotient.eq_zero_iff_mem.mpr hr
        change Ideal.Quotient.mk I r * x = 0
        rw [hr', zero_mul]
    simp [P, Module.support_eq_zeroLocus, hann, hquot]
  have transfer (A B : ModuleCat.{v} R)
      [Module.Finite R A] [Module.Finite R B]
      (hA : Module.support R A = PrimeSpectrum.zeroLocus I)
      (hB : Module.support R B = PrimeSpectrum.zeroLocus I)
      (n : ℕ) (h : ∀ i : ℕ, i < n → Subsingleton (Ext A M i)) :
      ∀ i : ℕ, i < n → Subsingleton (Ext B M i) := by
    obtain ⟨rs, h₁, h₂, h₃⟩ :=
      exists_isRegular_of_exists_subsingleton_ext I n M smul_lt A hA h
    intro i hi
    apply subsingleton_ext_of_exists_isRegular I B hB.subset M smul_lt rs
    all_goals first | assumption | omega
  have hvan (n : ℕ) :
      (∀ i : ℕ, i < n → Subsingleton (Ext N M i)) ↔
        (∀ i : ℕ, i < n → Subsingleton (Ext P M i)) :=
    ⟨transfer N P hsupp hP n, transfer P N hP hsupp n⟩
  change N.depth M = P.depth M
  rw [depth_eq_sSup_lt_top, depth_eq_sSup_lt_top]
  congr 1
  ext a
  rcases eq_or_ne a ⊤ with rfl | ha
  · simp
  · lift a to ℕ using ha
    simpa using hvan a
