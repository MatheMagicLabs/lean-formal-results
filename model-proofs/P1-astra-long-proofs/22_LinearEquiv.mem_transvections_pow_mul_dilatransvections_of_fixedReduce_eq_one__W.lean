/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     LinearEquiv.mem_transvections_pow_mul_dilatransvections_of_fixedReduce_eq_one
Source:      Mathlib @ d0a050ad6, Mathlib/LinearAlgebra/Transvection/Generation.lean, line 217
             (added after the model's training data; human proof 37 tactic steps)
Experiment:  P1-astra-long-proofs, arm W, solved after 4 call(s)
Prover:      gpt-6-astra
Setup:       GPT-6 Astra (Codex, effort medium), at most 10 calls per theorem: W = whole proof plus repair rounds;
             WT = W with read-only Mathlib sources to search; P = Lean-checked skeleton of have-steps, then one step per call
Check:       the proof replaced the human proof in the Mathlib file above; Lean reported
             0 errors and no `sorry`.
-/

theorem mem_transvections_pow_mul_dilatransvections_of_fixedReduce_eq_one
    {e : V ≃ₗ[K] V} (he : e.fixedReduce = 1) :
    e ∈ transvections K V ^ (finrank K (V ⧸ e.fixedSubmodule) - 1) * dilatransvections K V := by
  have hdiff : ∀ x, e x - x ∈ e.fixedSubmodule := by
    intro x
    have h := congrArg (fun g => g (Submodule.Quotient.mk x)) he
    change (Submodule.Quotient.mk (e x) : V ⧸ e.fixedSubmodule) =
      Submodule.Quotient.mk x at h
    simpa only [Submodule.Quotient.eq] using h
  generalize hn : finrank K (V ⧸ e.fixedSubmodule) = n
  induction n using Nat.strong_induction_on generalizing e with
  | h n ih =>
    by_cases hn₁ : n ≤ 1
    · have hd : e ∈ dilatransvections K V := by
        rw [mem_dilatransvections_iff_finrank]
        have hq := finrank_quotient_add_finrank e.fixedSubmodule
        have hr := finrank_range_add_finrank_ker (e.toLinearMap - LinearMap.id)
        rw [← fixedSubmodule_eq_ker] at hr
        omega
      simpa [Nat.sub_eq_zero_of_le hn₁] using hd
    · have hu : ∃ u : V, u ∉ e.fixedSubmodule := by
        by_contra! h
        have ht : e.fixedSubmodule = ⊤ :=
          top_unique (fun x _ => h x)
        have hq := finrank_quotient_add_finrank e.fixedSubmodule
        have hf : finrank K e.fixedSubmodule = finrank K V := by
          rw [ht, finrank_top]
        omega
      obtain ⟨u, hu⟩ := hu
      have hu₀ : e.fixedSubmodule.mkQ u ≠ 0 := by
        intro h
        have hm : u ∈ LinearMap.ker e.fixedSubmodule.mkQ := h
        rw [Submodule.ker_mkQ] at hm
        exact hu hm
      let b := Module.Free.chooseBasis K (V ⧸ e.fixedSubmodule)
      obtain ⟨i, hi⟩ : ∃ i, b.repr (e.fixedSubmodule.mkQ u) i ≠ 0 := by
        by_contra! h
        apply hu₀
        apply b.repr.injective
        ext i
        simpa using h i
      let g : Dual K (V ⧸ e.fixedSubmodule) :=
        { toFun := fun x => b.repr x i * (b.repr (e.fixedSubmodule.mkQ u) i)⁻¹
          map_add' := by
            intro x y
            simp [add_mul]
          map_smul' := by
            intro a x
            simp [smul_eq_mul, mul_assoc] }
      let f : Dual K V := g.comp e.fixedSubmodule.mkQ
      have hf₀ : e.fixedSubmodule ≤ LinearMap.ker f := by
        intro x hx
        have hx₀ : e.fixedSubmodule.mkQ x = 0 := by
          have hm : x ∈ LinearMap.ker e.fixedSubmodule.mkQ := by
            rw [Submodule.ker_mkQ]
            exact hx
          exact hm
        change g (e.fixedSubmodule.mkQ x) = 0
        rw [hx₀, map_zero]
      have hf : e.fixedSubmodule ⊔ K ∙ (e u - u) ≤ LinearMap.ker f := by
        apply sup_le hf₀
        rw [Submodule.span_singleton_le_iff_mem]
        exact hf₀ (hdiff u)
      have hfu : f u = 1 := by
        change b.repr (e.fixedSubmodule.mkQ u) i *
          (b.repr (e.fixedSubmodule.mkQ u) i)⁻¹ = 1
        exact mul_inv_cancel₀ hi
      have htfix := auxTransvection_mul_fixed (hf := hf) hfu
      have hdim := finrank_mod_auxTransvection_mul_fixed (hf := hf) hfu hu
      have hdiff' : ∀ x, (auxTransvection hf * e) x - x ∈
          (auxTransvection hf * e).fixedSubmodule := by
        intro x
        rw [htfix]
        apply Submodule.mem_sup_left
        have hu' : u - e u ∈ e.fixedSubmodule := by
          simpa only [neg_sub] using e.fixedSubmodule.neg_mem (hdiff u)
        convert e.fixedSubmodule.add_mem (hdiff x)
          (e.fixedSubmodule.smul_mem (f (e x)) hu') using 1 <;>
          simp only [LinearEquiv.mul_apply, auxTransvection, transvection.apply] <;>
          abel
      have he' : (auxTransvection hf * e).fixedReduce = 1 := by
        ext x
        refine Quotient.inductionOn x fun x => ?_
        change (Submodule.Quotient.mk ((auxTransvection hf * e) x) :
          V ⧸ (auxTransvection hf * e).fixedSubmodule) = Submodule.Quotient.mk x
        simpa only [Submodule.Quotient.eq] using hdiff' x
      have hlt : finrank K (V ⧸ (auxTransvection hf * e).fixedSubmodule) < n := by
        omega
      have hi : auxTransvection hf * e ∈
          transvections K V ^
            (finrank K (V ⧸ (auxTransvection hf * e).fixedSubmodule) - 1) *
              dilatransvections K V := by
        apply ih _ hlt <;> first | assumption | rfl
      have ht : (auxTransvection hf)⁻¹ ∈ transvections K V := by
        rw [inv_mem_transvections_iff]
        exact transvection_mem_transvections
      have hexp : n - 1 =
          (finrank K (V ⧸ (auxTransvection hf * e).fixedSubmodule) - 1) + 1 := by
        omega
      rw [hexp, pow_succ', mul_assoc]
      have hm := Set.mul_mem_mul ht hi
      simpa only [inv_mul_cancel_left] using hm
