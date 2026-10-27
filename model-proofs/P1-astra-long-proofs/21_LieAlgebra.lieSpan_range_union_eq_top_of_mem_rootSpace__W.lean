/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     LieAlgebra.lieSpan_range_union_eq_top_of_mem_rootSpace
Source:      Mathlib @ d0a050ad6, Mathlib/Algebra/Lie/Basis/Base.lean, line 153
             (added after the model's training data; human proof 41 tactic steps)
Experiment:  P1-astra-long-proofs, arm W, solved after 5 call(s)
Prover:      gpt-6-astra
Setup:       GPT-6 Astra (Codex, effort medium), at most 10 calls per theorem: W = whole proof plus repair rounds;
             WT = W with read-only Mathlib sources to search; P = Lean-checked skeleton of have-steps, then one step per call
Check:       the proof replaced the human proof in the Mathlib file above; Lean reported
             0 errors and no `sorry`.
-/

lemma lieSpan_range_union_eq_top_of_mem_rootSpace [IsKilling K L] (b : (rootSystem H).Base)
    (e f : b.support → L)
    (ef_sl2 : ∀ α : b.support, IsSl2Triple ((rootSystem H).coroot α : L) (e α) (f α))
    (e_mem :  ∀ α : b.support, e α ∈ rootSpace H α)
    (f_mem :  ∀ α : b.support, f α ∈ rootSpace H (-↑α)) :
    lieSpan K L (range e ∪ range f) = ⊤ := by
  let S := lieSpan K L (range e ∪ range f)
  have he (α : b.support) : e α ∈ S := subset_lieSpan (Or.inl (mem_range_self α))
  have hf (α : b.support) : f α ∈ S := subset_lieSpan (Or.inr (mem_range_self α))
  have hH : H ≤ S := by {
  rw [cartan_eq_lieSpan b];
  refine lieSpan_le.mpr ?_;
  rintro _ ⟨α, rfl⟩;
  change ((rootSystem H).coroot α : L) ∈ S;
  rw [← (ef_sl2 α).lie_e_f];
  exact S.lie_mem (he α) (hf α) }
  have hnonzero (α : H.root) : (α : Weight K H L).IsNonZero := by {
  have hα : ¬ (α : Weight K H L).IsZero := by simpa using α.property;
  exact hα }
  have hspan (α : Weight K H L) (hα : α.IsNonZero) (x : L) (hx : x ∈ rootSpace H α) (hx₀ : x ≠ 0) (hxS : x ∈ S) : (rootSpace H α).toSubmodule ≤ S.toSubmodule := by {
  rw [toSubmodule_rootSpace_eq_span α hα x hx₀ hx];
  exact Submodule.span_le.mpr (Set.singleton_subset_iff.mpr hxS) }
  have hadd (α β γ : H.root) (hγ : (γ : H → K) = (α : H → K) + (β : H → K)) (hα : (rootSpace H α).toSubmodule ≤ S.toSubmodule) (hβ : (rootSpace H β).toSubmodule ≤ S.toSubmodule) : (rootSpace H γ).toSubmodule ≤ S.toSubmodule := by {
  have hne : rootSpace H ((α : H → K) + (β : H → K)) ≠ ⊥ := by rw [← hγ]; exact γ.val.genWeightSpace_ne_bot;
  obtain ⟨x, hx, y, hy, hxy⟩ := exists_mem_rootSpace_lie_ne_zero (α := (α : Weight K H L)) (β := (β : Weight K H L)) (hnonzero α) hne;
  refine hspan γ (hnonzero γ) ⁅x, y⁆ ?_ hxy (S.lie_mem (hα hx) (hβ hy));
  simp only [Weight.coe_coe] at hγ;
  rw [hγ];
  exact lie_mem_genWeightSpace_of_mem_genWeightSpace hx hy }
  let P : H.root → Prop := fun α ↦ (rootSpace H α).toSubmodule ≤ S.toSubmodule ∧ (rootSpace H (-α)).toSubmodule ≤ S.toSubmodule
  have hbase (α : H.root) (hα : α ∈ b.support) : P α := by {
  let a : b.support := ⟨α, hα⟩;
  have hp := hspan (α : Weight K H L) (hnonzero α) (e a) (e_mem a) (ef_sl2 a).e_ne_zero (he a);
  have hm := hspan (-(α : Weight K H L)) (hnonzero α).neg (f a) (by simpa using f_mem a) (ef_sl2 a).f_ne_zero (hf a);
  exact ⟨hp, by simpa only [val_neg_root, Weight.toLinear_neg, LinearMap.coe_neg, Weight.coe_coe, Weight.coe_neg] using hm⟩ }
  have hneg (α : H.root) (hα : P α) : P ((rootSystem H).reflectionPerm α α) := by {
  rw [rootSystem_reflectionPerm_self_eq_neg];
  change (rootSpace H (-α)).toSubmodule ≤ S.toSubmodule ∧ (rootSpace H (- -α)).toSubmodule ≤ S.toSubmodule;
  simpa only [neg_neg] using hα.symm }
  have hstep (α β γ : H.root) (hγ : (rootSystem H).root γ = (rootSystem H).root α + (rootSystem H).root β) (hα : P α) (hβ : β ∈ b.support) : P γ := by {
  have hβ' := hbase β hβ;
  have hγ' : (γ : H → K) = (α : H → K) + (β : H → K) := congrArg (fun φ : H →ₗ[K] K ↦ (φ : H → K)) hγ;
  have hn : (-γ : H → K) = (-α : H → K) + (-β : H → K) := by simpa only [val_neg_root, Weight.toLinear_neg, LinearMap.coe_neg, Weight.coe_coe, Weight.coe_neg, neg_add] using congrArg Neg.neg hγ';
  exact ⟨hadd α β γ hγ' hα.1 hβ'.1, hadd (-α) (-β) (-γ) hn hα.2 hβ'.2⟩ }
  have hroot (α : H.root) : P α := b.induction_add α hneg hbase hstep
  have hweight (χ : Weight K H L) : (genWeightSpace L χ).toSubmodule ≤ S.toSubmodule := by {
  by_cases hχ : χ.IsZero;
  · have hzero : (χ : H → K) = 0 := hχ; change (rootSpace H χ).toSubmodule ≤ S.toSubmodule; rw [hzero, rootSpace_zero_eq]; exact hH
  · have hχ' : χ ∈ H.root := by { simpa using hχ }; exact (hroot ⟨χ, hχ'⟩).1 }
  have htop : (⨆ χ : Weight K H L, (genWeightSpace L χ).toSubmodule) = ⊤ := LieSubmodule.iSup_toSubmodule_eq_top.mpr (iSup_genWeightSpace_eq_top' K H L)
  apply LieSubalgebra.toSubmodule_injective
  change S.toSubmodule = ⊤
  apply top_unique
  rw [← htop]
  exact iSup_le hweight
