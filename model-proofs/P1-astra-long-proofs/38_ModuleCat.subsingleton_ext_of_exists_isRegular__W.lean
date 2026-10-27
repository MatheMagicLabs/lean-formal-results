/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     ModuleCat.subsingleton_ext_of_exists_isRegular
Source:      Mathlib @ d0a050ad6, Mathlib/RingTheory/Depth/Rees.lean, line 101
             (added after the model's training data; human proof 25 tactic steps)
Experiment:  P1-astra-long-proofs, arm W, solved after 3 call(s)
Prover:      gpt-6-astra
Setup:       GPT-6 Astra (Codex, effort medium), at most 10 calls per theorem: W = whole proof plus repair rounds;
             WT = W with read-only Mathlib sources to search; P = Lean-checked skeleton of have-steps, then one step per call
Check:       the proof replaced the human proof in the Mathlib file above; Lean reported
             0 errors and no `sorry`.
-/

lemma subsingleton_ext_of_exists_isRegular [Small.{v} R] [IsNoetherianRing R] (I : Ideal R)
    (N : ModuleCat.{v} R) [Nfin : Module.Finite R N]
    (Nsupp : Module.support R N ⊆ PrimeSpectrum.zeroLocus I)
    (M : ModuleCat.{v} R) [Module.Finite R M] (smul_lt : I • (⊤ : Submodule R M) < ⊤)
    (rs : List R) (mem : ∀ r ∈ rs, r ∈ I) (reg : IsRegular M rs) :
    ∀ i < rs.length, Subsingleton (Ext N M i) := by
  classical
  induction rs generalizing M with
  | nil => simp
  | cons x rs ih =>
    have hreg : IsSMulRegular M x ∧ IsRegular (QuotSMulTop x M) rs := by simpa using reg
    have hxI : x ∈ I := mem x (by simp)
    have hmem : ∀ r ∈ rs, r ∈ I := fun r hr => mem r (by simp [hr])
    have hrad : x ∈ (Module.annihilator R N).radical := by
      rw [Module.support_eq_zeroLocus, PrimeSpectrum.zeroLocus_subset_zeroLocus_iff] at Nsupp
      first | exact Nsupp hxI | exact Nsupp (Ideal.le_radical hxI)
    obtain ⟨k, hk⟩ := hrad
    have hquot : ∀ i < rs.length, Subsingleton (Ext N ↧(QuotSMulTop x M) i) :=
      ih ↧(QuotSMulTop x M)
        (smul_top_quotSMulTop_ne_top_of_smul_top_ne_top hxI smul_lt.ne).lt_top
        hmem hreg.2
    intro i hi
    cases i with
    | zero =>
      have hlin : Subsingleton (N →ₗ[R] M) :=
        subsingleton_linearMap_iff.mpr ⟨x ^ k, hk, hreg.1.pow k⟩
      letI := hlin
      have hhom : Subsingleton (N ⟶ M) := ModuleCat.homAddEquiv.subsingleton
      exact Ext.addEquiv₀.subsingleton_congr.mpr hhom
    | succ i =>
      have hzero := AddCommGrpCat.isZero_of_iff_subsingleton.mpr (hquot i (by simpa using hi))
      have hexact := Ext.covariant_sequence_exact₁' N hreg.1.smulShortComplex_shortExact i (i + 1) rfl
      have hmono := hexact.mono_g (hzero.eq_zero_of_src _)
      have hregular : IsSMulRegular (Ext N M (i + 1)) x := by
        intro a b hab
        apply (AddCommGrpCat.mono_iff_injective _).mp hmono
        change a.comp (Ext.mk₀ (x • 𝟙 M)) (add_zero (i + 1)) =
          b.comp (Ext.mk₀ (x • 𝟙 M)) (add_zero (i + 1))
        first
        | simpa [Ext.mk₀_smul, Ext.comp_smul] using hab
        | simpa [Ext.smul_def] using hab
        | simpa [Ext.smul_def'] using hab
      have hscalar : (x ^ k) • (𝟙 N) = (0 : N ⟶ N) := by
        apply ModuleCat.hom_ext
        ext y
        exact (Module.mem_annihilator.mp hk) y
      have hvanish : ∀ e : Ext N M (i + 1), (x ^ k) • e = 0 := by
        intro e
        have he := congrArg
          (fun f : N ⟶ N => (Ext.addEquiv₀.symm f).comp e (zero_add (i + 1)))
          hscalar
        first
        | simpa [Ext.mk₀_smul, Ext.smul_comp] using he
        | simpa [Ext.smul_def] using he
        | simpa [Ext.smul_def'] using he
      refine ⟨fun a b => (hregular.pow k) ?_⟩
      change (x ^ k) • a = (x ^ k) • b
      rw [hvanish a, hvanish b]
