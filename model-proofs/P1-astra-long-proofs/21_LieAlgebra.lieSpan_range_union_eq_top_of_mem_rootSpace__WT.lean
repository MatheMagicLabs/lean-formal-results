/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     LieAlgebra.lieSpan_range_union_eq_top_of_mem_rootSpace
Source:      Mathlib @ d0a050ad6, Mathlib/Algebra/Lie/Basis/Base.lean, line 153
             (added after the model's training data; human proof 41 tactic steps)
Experiment:  P1-astra-long-proofs, arm WT, solved after 2 call(s)
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
  classical
  let S := lieSpan K L (range e ∪ range f)
  have he (i : b.support) : e i ∈ S :=
    subset_lieSpan (Or.inl (mem_range_self i))
  have hf (i : b.support) : f i ∈ S :=
    subset_lieSpan (Or.inr (mem_range_self i))
  have hH : H ≤ S := by
    rw [cartan_eq_lieSpan b]
    apply lieSpan_le.mpr
    rintro _ ⟨i, rfl⟩
    change ((rootSystem H).coroot i : L) ∈ S
    rw [← (ef_sl2 i).lie_e_f]
    exact S.lie_mem (he i) (hf i)
  have hspan (α : Weight K H L) (hα : α.IsNonZero)
      (x : L) (hx : x ∈ rootSpace H α) (hx₀ : x ≠ 0) (hxS : x ∈ S) :
      (rootSpace H α).toSubmodule ≤ S.toSubmodule := by
    rw [toSubmodule_rootSpace_eq_span α hα x hx₀ hx,
      Submodule.span_singleton_le_iff_mem]
    exact hxS
  have hadd (α β γ : Weight K H L) (hα : α.IsNonZero)
      (hγ : γ.IsNonZero) (h : (γ : H → K) = α + β)
      (ha : (rootSpace H α).toSubmodule ≤ S.toSubmodule)
      (hb : (rootSpace H β).toSubmodule ≤ S.toSubmodule) :
      (rootSpace H γ).toSubmodule ≤ S.toSubmodule := by
    have hn : rootSpace H (α + β) ≠ ⊥ := by
      rw [← h]
      exact γ.genWeightSpace_ne_bot
    obtain ⟨x, hx, y, hy, hxy⟩ := exists_mem_rootSpace_lie_ne_zero hα hn
    apply hspan γ hγ ⁅x, y⁆
    · rw [h]
      exact lie_mem_genWeightSpace_of_mem_genWeightSpace hx hy
    · exact hxy
    · exact S.lie_mem (ha hx) (hb hy)
  have hbase (i : H.root) (hi : i ∈ b.support) :
      (rootSpace H i.val).toSubmodule ≤ S.toSubmodule ∧
      (rootSpace H (-i.val)).toSubmodule ≤ S.toSubmodule := by
    let j : b.support := ⟨i, hi⟩
    constructor
    · exact hspan i.val (H.isNonZero_coe_root i) (e j)
        (e_mem j) (ef_sl2 j).e_ne_zero (he j)
    · exact hspan (-i.val) (H.isNonZero_coe_root i).neg (f j)
        (f_mem j) (ef_sl2 j).f_ne_zero (hf j)
  have hall (i : H.root) :
      (rootSpace H i.val).toSubmodule ≤ S.toSubmodule ∧
      (rootSpace H (-i.val)).toSubmodule ≤ S.toSubmodule := by
    apply b.induction_add i
    · intro j hj
      simpa only [rootSystem_reflectionPerm_self_eq_neg, val_neg_root,
        Weight.coe_neg, neg_neg] using hj.symm
    · exact hbase
    · intro j k l h hj hk
      have h' : (l.val : H → K) = j.val + k.val := by
        exact congrArg (fun q : H →ₗ[K] K => (q : H → K)) h
      constructor
      · exact hadd j.val k.val l.val (H.isNonZero_coe_root j)
          (H.isNonZero_coe_root l) h' hj.1 (hbase k hk).1
      · apply hadd (-j.val) (-k.val) (-l.val)
          (H.isNonZero_coe_root j).neg (H.isNonZero_coe_root l).neg
          _ hj.2 (hbase k hk).2
        simpa only [Weight.coe_neg, neg_add] using congrArg Neg.neg h'
  have htop := congrArg LieSubmodule.toSubmodule
    (cartan_sup_iSup_rootSpace_eq_top (K := K) (L := L) (H := H))
  simp only [LieSubmodule.sup_toSubmodule, LieSubmodule.iSup_toSubmodule,
    LieSubmodule.top_toSubmodule] at htop
  have hS : (⊤ : Submodule K L) ≤ S.toSubmodule := by
    rw [← htop]
    refine sup_le hH (iSup_le fun α => iSup_le fun hα => ?_)
    exact (hall ⟨α, by simpa only [LieSubalgebra.root, Finset.mem_filter,
      Finset.mem_univ, true_and] using hα⟩).1
  apply top_unique
  intro x _
  exact hS (Submodule.mem_top)
