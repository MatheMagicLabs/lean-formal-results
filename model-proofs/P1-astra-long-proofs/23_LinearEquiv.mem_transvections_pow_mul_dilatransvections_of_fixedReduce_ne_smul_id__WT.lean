/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     LinearEquiv.mem_transvections_pow_mul_dilatransvections_of_fixedReduce_ne_smul_id
Source:      Mathlib @ d0a050ad6, Mathlib/LinearAlgebra/Transvection/Generation.lean, line 417
             (added after the model's training data; human proof 41 tactic steps)
Experiment:  P1-astra-long-proofs, arm WT, solved after 2 call(s)
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
  have main : ∀ n : ℕ, ∀ e : V ≃ₗ[K] V,
      (∀ a : K, ∃ x, e.fixedReduce x ≠ a • x) →
      finrank K (V ⧸ e.fixedSubmodule) = n →
      e ∈ transvections K V ^ (n - 1) * dilatransvections K V := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro e he hn
      by_cases hnsmall : n ≤ 1
      · have hsub : n - 1 = 0 := by omega
        simp only [hsub, pow_zero, one_mul]
        rw [mem_dilatransvections_iff_finrank_quotient]
        omega
      have hnlarge : 1 < finrank K (V ⧸ e.fixedSubmodule) := by omega
      obtain ⟨f, v, hv, hf, hfv⟩ := exists_dual_of_fixedReduce_ne_smul he hnlarge
      have hvnot : v ∉ e.fixedSubmodule := by
        intro hv'
        have hz : f v = 0 := LinearMap.mem_ker.mp (hf (mem_sup_left hv'))
        rw [hfv] at hz
        exact one_ne_zero hz
      have hdim := finrank_quotient_sup_span_singleton hvnot
      have choice : ∃ (f' : Dual K V)
          (hf' : e.fixedSubmodule ⊔ K ∙ (e v - v) ≤ LinearMap.ker f'),
          f' v = 1 ∧
          (2 < n → ∀ a : K, ∃ x,
            (auxTransvection hf' * e).fixedReduce x ≠ a • x) := by
        by_cases hlarge : 2 < n
        · by_cases ha : ∀ a : K, ∃ x,
              (auxTransvection hf * e).fixedReduce x ≠ a • x
          · exact ⟨f, hf, hfv, fun _ ↦ ha⟩
          push_neg at ha
          obtain ⟨a, ha⟩ := ha
          have htop : e.fixedSubmodule ⊔ K ∙ (e v - v) ⊔ K ∙ v < ⊤ := by
            rw [sup_assoc, sup_comm (K ∙ (e v - v)) (K ∙ v), ← sup_assoc]
            apply sup_span_singleton_lt_top
            omega
          obtain ⟨g, hg0, hg⟩ :=
            Submodule.exists_dual_map_eq_bot_of_lt_top htop inferInstance
          rw [← LinearMap.le_ker_iff_map] at hg
          have hgv : g v = 0 :=
            LinearMap.mem_ker.mp (hg (mem_sup_right (mem_span_singleton_self v)))
          have hfg : e.fixedSubmodule ⊔ K ∙ (e v - v) ≤
              LinearMap.ker (f + g) := by
            intro x hx
            rw [LinearMap.mem_ker, LinearMap.add_apply,
              LinearMap.mem_ker.mp (hf hx),
              LinearMap.mem_ker.mp (hg (mem_sup_left hx)), add_zero]
          have hfgv : (f + g) v = 1 := by
            simp only [LinearMap.add_apply, hfv, hgv, add_zero]
          refine ⟨f + g, hfg, hfgv, ?_⟩
          intro _
          by_contra hb
          push_neg at hb
          obtain ⟨b, hb⟩ := hb
          exact not_forall_fixedReduce_eq_smul hv hfv hfgv hg0 htop ha hb
        · exact ⟨f, hf, hfv, fun hh ↦ False.elim (hlarge hh)⟩
      obtain ⟨f', hf', hfv', hgood⟩ := choice
      have hr := finrank_mod_auxTransvection_mul_fixed (hf := hf') hfv' hvnot
      let m := finrank K (V ⧸ (auxTransvection hf' * e).fixedSubmodule)
      have hm : m + 1 = n := by
        simpa only [m, hn] using hr
      have hmem : auxTransvection hf' * e ∈
          transvections K V ^ (m - 1) * dilatransvections K V := by
        by_cases hmsmall : m ≤ 1
        · have hsub : m - 1 = 0 := by omega
          simp only [hsub, pow_zero, one_mul]
          rw [mem_dilatransvections_iff_finrank_quotient]
          exact hmsmall
        · exact ih m (by omega) (auxTransvection hf' * e)
            (hgood (by omega)) rfl
      have hexp : n - 1 = (m - 1) + 1 := by omega
      rw [hexp, pow_succ', mul_assoc]
      refine Set.mem_mul.mpr ⟨(auxTransvection hf')⁻¹, ?_,
        auxTransvection hf' * e, hmem, by simp⟩
      rw [inv_mem_transvections_iff]
      exact mem_transvections _
  exact main _ e he rfl
