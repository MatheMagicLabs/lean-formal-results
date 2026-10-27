/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     ModuleCat.depth_eq_sSup_length_isRegular
Source:      Mathlib @ a02a63c2, Mathlib/RingTheory/Depth/Basic.lean, line 316
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  O2-repair-vs-resample, arm B, verified in round 2 (round 0 = first attempt)
Prover:      claude-opus-5-5
Setup:       Opus 5.5: arm B = one attempt plus up to 3 repair rounds with Lean error messages; arm A = 4 independent attempts (attempt k)
Check:       the proof replaced the human proof in the Mathlib file above; Lean reported
             0 errors and no `sorry`; sorry/admit/native_decide/search tactics were rejected.
-/

-- (context: the Mathlib file above this declaration)
lemma depth_eq_sSup_length_isRegular [IsNoetherianRing R] (I : Ideal R)
    (N M : ModuleCat.{v} R) [Module.Finite R M] [Module.Finite R N]
    [Nontrivial N] (smul_lt : I • (⊤ : Submodule R M) < ⊤)
    (hsupp : Module.support R N = PrimeSpectrum.zeroLocus I) :
    N.depth M = sSup {(List.length rs : ℕ∞) | (rs : List R)
      (_ : RingTheory.Sequence.IsRegular M rs) (_ : ∀ r ∈ rs, r ∈ I) } := by
  have key (n : ℕ) : (∀ i < n, Subsingleton (Ext N M i)) ↔ ∃ rs : List R, rs.length = n ∧
      (∀ r ∈ rs, r ∈ I) ∧ RingTheory.Sequence.IsRegular M rs := by
    have tfae := exists_isRegular_tfae I n M smul_lt
    constructor
    · intro h
      have h3 : ∃ N' : ModuleCat.{v} R, Nontrivial N' ∧ Module.Finite R N' ∧
          Module.support R N' = PrimeSpectrum.zeroLocus I ∧
          ∀ i < n, Subsingleton (Ext N' M i) := ⟨N, ‹_›, ‹_›, hsupp, h⟩
      have h34 := tfae.out 3 4
      exact h34.mp h3
    · intro hrs
      have h1 := (tfae.out 1 4).mpr hrs
      exact h1 N ‹_› ‹_› (le_of_eq hsupp)
  rw [depth_eq_sSup_lt_top]
  congr 1
  ext n
  induction n with
  | top => simp
  | coe n =>
    simp only [Set.mem_setOf_eq]
    constructor
    · rintro ⟨-, h⟩
      obtain ⟨rs, len, mem, reg⟩ := (key n).mp (fun i hi => h i (by exact_mod_cast hi))
      exact ⟨rs, reg, mem, by rw [len]⟩
    · rintro ⟨rs, reg, mem, len⟩
      refine ⟨by simp, ?_⟩
      have := (key n).mpr ⟨rs, by exact_mod_cast len, mem, reg⟩
      intro i hi
      exact this i (by exact_mod_cast hi)
