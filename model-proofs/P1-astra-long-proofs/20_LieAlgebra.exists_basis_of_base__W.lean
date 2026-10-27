/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     LieAlgebra.exists_basis_of_base
Source:      Mathlib @ d0a050ad6, Mathlib/Algebra/Lie/Basis/Base.lean, line 211
             (added after the model's training data; human proof 25 tactic steps)
Experiment:  P1-astra-long-proofs, arm W, solved after 3 call(s)
Prover:      gpt-6-astra
Setup:       GPT-6 Astra (Codex, effort medium), at most 10 calls per theorem: W = whole proof plus repair rounds;
             WT = W with read-only Mathlib sources to search; P = Lean-checked skeleton of have-steps, then one step per call
Check:       the proof replaced the human proof in the Mathlib file above; Lean reported
             0 errors and no `sorry`.
-/

lemma exists_basis_of_base [IsKilling K L] (b : (rootSystem H).Base) :
    ∃ B : Basis b.support H, B.A = b.cartanMatrix ∧ (∀ i, B.h i = (rootSystem H).coroot i) := by
  have nonZero (α : b.support) : (α : Weight K H L).IsNonZero := H.isNonZero_coe_root (α : H.root)
  choose h e f ef_sl2 e_mem f_mem using fun α ↦ exists_isSl2Triple_of_weight_isNonZero (nonZero α)
  have h_coroot (i : b.support) : h i = (rootSystem H).coroot i := (ef_sl2 i).h_eq_coroot (nonZero i) (e_mem i) (f_mem i)
  simp_rw [h_coroot] at ef_sl2
  refine ⟨{
  A := b.cartanMatrix
  h := fun i ↦ (rootSystem H).coroot i
  e := e
  f := f
  cartan_eq_lieSpan := cartan_eq_lieSpan b
  linInd := b.linearIndepOn_coroot.map_injOn H.incl.toLinearMap (by simp)
  nondegen := b.cartanMatrix_nondegenerate
  sl2 := ef_sl2
  lie_h_h := by simp [← coe_bracket, trivial_lie_zero]
  span_ef := lieSpan_range_union_eq_top_of_mem_rootSpace b e f ef_sl2 e_mem f_mem
  lie_h_e := ?_
  lie_h_f := ?_
  lie_e_f_ne := ?_ }, rfl, fun _ ↦ rfl⟩
  · {
  intro i j
  have hc : (b.cartanMatrix i j : K) = algebraMap ℤ K (b.cartanMatrix i j) := by simp
  rw [← LieSubalgebra.coe_bracket_of_module, lie_eq_smul_of_mem_rootSpace (e_mem i), ← Int.cast_smul_eq_zsmul K, hc, Base.cartanMatrix, Base.cartanMatrixIn_def, algebraMap_pairingIn, rootSystem_coroot_apply, rootSystem_pairing_apply]
  }
  · {
  intro i j
  have hc : (b.cartanMatrix i j : K) = algebraMap ℤ K (b.cartanMatrix i j) := by simp
  rw [neg_smul, ← LieSubalgebra.coe_bracket_of_module, lie_eq_smul_of_mem_rootSpace (f_mem i), ← Int.cast_smul_eq_zsmul K, hc, Base.cartanMatrix, Base.cartanMatrixIn_def, algebraMap_pairingIn, rootSystem_coroot_apply, rootSystem_pairing_apply, Pi.neg_apply, neg_smul]
  }
  · {
  intro i j hij
  set χ : H → K := ⇑i.val.val - ⇑j.val.val with hχ
  have hχ₀ : χ ≠ 0 := by intro hz; apply hij; apply Subtype.ext; apply Subtype.ext; apply DFunLike.coe_injective; exact sub_eq_zero.mp hz
  have hbot : rootSpace H χ = ⊥ := by
  {
  have hn := b.sub_notMem_range_root i.property j.property
  simp only [rootSystem_root_apply, mem_range, Subtype.exists, Finset.mem_filter, Finset.mem_univ, true_and, exists_prop, not_exists, not_and, ne_eq] at hn
  contrapose! hn
  exact ⟨⟨χ, hn⟩, hχ₀, LinearMap.ext fun x ↦ by simp [hχ]⟩
  }
  have hmem : ⁅e i, f j⁆ ∈ rootSpace H χ := by rw [hχ, sub_eq_add_neg]; exact mapsTo_toEnd_genWeightSpace_add_of_mem_rootSpace K L H L _ _ (e_mem i) (f_mem j)
  simpa [hbot] using hmem
  }
