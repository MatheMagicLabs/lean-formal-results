/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     LinearEquiv.mem_transvections_pow_mul_dilatransvections_of_fixedReduce_ne_smul_id
Source:      Mathlib @ d0a050ad6, Mathlib/LinearAlgebra/Transvection/Generation.lean, line 417
             (added after the model's training data; human proof 41 tactic steps)
Experiment:  P1-astra-long-proofs, arm W, solved after 3 call(s)
Prover:      gpt-6-astra
Setup:       GPT-6 Astra (Codex, effort medium), at most 10 calls per theorem: W = whole proof plus repair rounds;
             WT = W with read-only Mathlib sources to search; P = Lean-checked skeleton of have-steps, then one step per call
Check:       the proof replaced the human proof in the Mathlib file above; Lean reported
             0 errors and no `sorry`.
-/

theorem mem_transvections_pow_mul_dilatransvections_of_fixedReduce_ne_smul_id
    {e : V ≃ₗ[K] V}
    (he : ∀ a : K, ∃ x, e.fixedReduce x ≠ a • x) :
    e ∈ transvections K V ^ (finrank K (V ⧸ e.fixedSubmodule) - 1) * dilatransvections K V := by
  classical
  suffices H : ∀ n : ℕ, ∀ e : V ≃ₗ[K] V, finrank K (V ⧸ e.fixedSubmodule) = n → (∀ a : K, ∃ x, e.fixedReduce x ≠ a • x) → e ∈ transvections K V ^ (finrank K (V ⧸ e.fixedSubmodule) - 1) * dilatransvections K V by exact H _ e rfl he
  intro n
  induction n using Nat.strong_induction_on
  rename_i n ih
  intro e hn he
  by_cases hs : finrank K (V ⧸ e.fixedSubmodule) ≤ 1
  swap
  obtain ⟨f, v, hv, hf, hfv⟩ := exists_dual_of_fixedReduce_ne_smul he (by omega)
  have hv_notMem : v ∉ e.fixedSubmodule := by intro h; have hz : f v = 0 := hf (mem_sup_left h); rw [hfv] at hz; exact one_ne_zero hz
  have finish (p : Dual K V) (hp : e.fixedSubmodule ⊔ K ∙ (e v - v) ≤ LinearMap.ker p) (hpv : p v = 1) (ht : auxTransvection hp * e ∈ transvections K V ^ (finrank K (V ⧸ (auxTransvection hp * e).fixedSubmodule) - 1) * dilatransvections K V) : e ∈ transvections K V ^ (finrank K (V ⧸ e.fixedSubmodule) - 1) * dilatransvections K V := by have hd := finrank_mod_auxTransvection_mul_fixed (hf := hp) hpv hv_notMem; have hexp : finrank K (V ⧸ e.fixedSubmodule) - 1 = (finrank K (V ⧸ (auxTransvection hp * e).fixedSubmodule) - 1) + 1 := (by omega); rw [hexp, pow_succ', mul_assoc]; refine Set.mem_mul.mpr ⟨(auxTransvection hp)⁻¹, ?_, auxTransvection hp * e, ht, by simp⟩; rw [inv_mem_transvections_iff]; apply mem_transvections
  have finish_nonhom (p : Dual K V) (hp : e.fixedSubmodule ⊔ K ∙ (e v - v) ≤ LinearMap.ker p) (hpv : p v = 1) (ht : ∀ a : K, ∃ x, (auxTransvection hp * e).fixedReduce x ≠ a • x) : e ∈ transvections K V ^ (finrank K (V ⧸ e.fixedSubmodule) - 1) * dilatransvections K V := by apply finish p hp hpv; have hd := finrank_mod_auxTransvection_mul_fixed (hf := hp) hpv hv_notMem; exact ih _ (by omega) (auxTransvection hp * e) rfl ht
  by_cases htwo : finrank K (V ⧸ e.fixedSubmodule) ≤ 2
  swap
  have hdim := finrank_quotient_sup_span_singleton hv_notMem
  have hne_top : e.fixedSubmodule ⊔ K ∙ (e v - v) ⊔ K ∙ v < ⊤ := by rw [sup_right_comm]; exact sup_span_singleton_lt_top (e v - v) (by omega)
  obtain ⟨w, hw⟩ : ∃ w : V, w ∉ e.fixedSubmodule ⊔ K ∙ (e v - v) ⊔ K ∙ v := by by_contra! h; exact hne_top.ne (Submodule.eq_top_iff'.mpr h)
  obtain ⟨g, hgw, hg⟩ := exists_dual_map_eq_bot_of_notMem hw inferInstance
  rw [← LinearMap.le_ker_iff_map] at hg
  have hg0 : g ≠ 0 := by intro h; apply hgw; simp [h]
  have hgv : g v = 0 := hg (mem_sup_right (mem_span_singleton_self _))
  have hfg : e.fixedSubmodule ⊔ K ∙ (e v - v) ≤ LinearMap.ker (f + g) := by intro x hx; change f x + g x = 0; rw [show f x = 0 from hf hx, show g x = 0 from hg (mem_sup_left hx), add_zero]
  have hfgv : (f + g) v = 1 := by simp [hfv, hgv]
  by_cases ht : ∀ a : K, ∃ x, (auxTransvection hf * e).fixedReduce x ≠ a • x
  swap
  push_neg at ht
  obtain ⟨a, ha⟩ := ht
  have ht' : ∀ b : K, ∃ x, (auxTransvection hfg * e).fixedReduce x ≠ b • x := by intro b; by_contra! hb; exact not_forall_fixedReduce_eq_smul (hf := hf) (hg := hfg) hv hfv hfgv hg0 hne_top ha hb
  exact finish_nonhom (f + g) hfg hfgv ht'
  exact finish_nonhom f hf hfv ht
  apply finish f hf hfv
  have hd := finrank_mod_auxTransvection_mul_fixed (hf := hf) hfv hv_notMem
  have ht : finrank K (V ⧸ (auxTransvection hf * e).fixedSubmodule) ≤ 1 := by omega
  rw [Nat.sub_eq_zero_of_le ht, pow_zero, one_mul, mem_dilatransvections_iff_finrank_quotient]
  exact ht
  rw [Nat.sub_eq_zero_of_le hs, pow_zero, one_mul, mem_dilatransvections_iff_finrank_quotient]
  exact hs
