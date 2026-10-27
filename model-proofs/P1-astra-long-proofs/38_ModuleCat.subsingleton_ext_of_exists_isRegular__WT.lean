/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     ModuleCat.subsingleton_ext_of_exists_isRegular
Source:      Mathlib @ d0a050ad6, Mathlib/RingTheory/Depth/Rees.lean, line 101
             (added after the model's training data; human proof 25 tactic steps)
Experiment:  P1-astra-long-proofs, arm WT, solved after 4 call(s)
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
  rw [Module.support_eq_zeroLocus, PrimeSpectrum.zeroLocus_subset_zeroLocus_iff] at Nsupp
  induction rs generalizing M with
  | nil => simp
  | cons r rs ih => obtain ⟨hr, hreg⟩ := (isRegular_cons_iff M r rs).mp reg; have hrI := mem r (List.mem_cons_self ..); obtain ⟨k, hk⟩ := Nsupp hrI; have hmem : ∀ s ∈ rs, s ∈ I := fun s hs ↦ mem s (List.mem_cons_of_mem r hs); have hquot := ih ↧(QuotSMulTop r M) (smul_top_quotSMulTop_ne_top_of_smul_top_ne_top hrI smul_lt.ne).lt_top hmem hreg; intro i hi; cases i with | zero => exact Ext.addEquiv₀.subsingleton_congr.mpr (ModuleCat.homAddEquiv.subsingleton_congr.mpr ((hr.pow k).linearMap_subsingleton_of_mem_annihilator hk)) | succ i => have hzero := AddCommGrpCat.isZero_of_iff_subsingleton.mpr (hquot i (by simpa using hi)); have hmono := (Ext.covariant_sequence_exact₁' N hr.smulShortComplex_shortExact i (i + 1) rfl).mono_g (hzero.eq_zero_of_src _); have hregular : IsSMulRegular (Ext N M (i + 1)) r := (Ext.postcomp_smul_id_mono_iff r (i + 1)).mp (by with_unfolding_all exact hmono); have hpower := (Ext.postcomp_smul_id_mono_iff (M := M) (N := N) (r ^ k) (i + 1)).mpr (hregular.pow k); rw [Ext.postcomp_smul_id_eq_zero_of_mem_annihilator hk] at hpower; have hinj := (AddCommGrpCat.mono_iff_injective _).mp hpower; exact ⟨fun a b ↦ hinj (by simp)⟩
