/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     LieAlgebra.exists_basis_of_base
Source:      Mathlib @ d0a050ad6, Mathlib/Algebra/Lie/Basis/Base.lean, line 211
             (added after the model's training data; human proof 25 tactic steps)
Experiment:  P1-astra-long-proofs, arm WT, solved after 3 call(s)
Prover:      gpt-6-astra
Setup:       GPT-6 Astra (Codex, effort medium), at most 10 calls per theorem: W = whole proof plus repair rounds;
             WT = W with read-only Mathlib sources to search; P = Lean-checked skeleton of have-steps, then one step per call
Check:       the proof replaced the human proof in the Mathlib file above; Lean reported
             0 errors and no `sorry`.
-/

lemma exists_basis_of_base [IsKilling K L] (b : (rootSystem H).Base) :
    ∃ B : Basis b.support H, B.A = b.cartanMatrix ∧ (∀ i, B.h i = (rootSystem H).coroot i) := by
  classical
  have hex (i : b.support) :
      ∃ e f : L, IsSl2Triple ((rootSystem H).coroot i : L) e f ∧
        e ∈ rootSpace H i ∧ f ∈ rootSpace H (-↑i) := by
    obtain ⟨h, e, f, ht, he, hf⟩ :=
      exists_isSl2Triple_of_weight_isNonZero (H.isNonZero_coe_root i)
    have hh := ht.h_eq_coroot (H.isNonZero_coe_root i) he hf
    exact ⟨e, f, hh ▸ ht, he, hf⟩
  choose e f ht he hf using hex
  have hc (i j : b.support) :
      ((b.cartanMatrix i j : ℤ) : K) =
        (i : Weight K H L) ((rootSystem H).coroot j) := by
    simpa using b.algebraMap_cartanMatrixIn_apply ℤ i j
  have hlin : LinearIndependent K
      (fun i : b.support ↦ ((rootSystem H).coroot i : L)) := by
    have hi := b.toCoweightBasis.linearIndependent.map' H.toSubmodule.subtype
      (LinearMap.ker_eq_bot.mpr Subtype.val_injective)
    change LinearIndependent K (fun i : b.support ↦ (b.toCoweightBasis i : L)) at hi
    simpa only [RootPairing.Base.toCoweightBasis_apply] using hi
  have hhh (i j : b.support) :
      ⁅((rootSystem H).coroot i : L), ((rootSystem H).coroot j : L)⁆ = 0 := by
    rw [← LieSubalgebra.coe_bracket, trivial_lie_zero]
    rfl
  have hhe (i j : b.support) :
      ⁅((rootSystem H).coroot j : L), e i⁆ = b.cartanMatrix i j • e i := by
    calc
      _ = (i : Weight K H L) ((rootSystem H).coroot j) • e i :=
        lie_eq_smul_of_mem_rootSpace (he i) ((rootSystem H).coroot j)
      _ = _ := by rw [← hc, Int.cast_smul_eq_zsmul]
  have hhf (i j : b.support) :
      ⁅((rootSystem H).coroot j : L), f i⁆ = -b.cartanMatrix i j • f i := by
    calc
      _ = -(i : Weight K H L) ((rootSystem H).coroot j) • f i :=
        lie_eq_smul_of_mem_rootSpace (hf i) ((rootSystem H).coroot j)
      _ = _ := by rw [← hc, ← Int.cast_neg, Int.cast_smul_eq_zsmul]
  have hef (i j : b.support) (hij : i ≠ j) : ⁅e i, f j⁆ = 0 := by
    have hbot :
        rootSpace H ((i : H →ₗ[K] K) - (j : H →ₗ[K] K)) = ⊥ := by
      by_contra hn
      let α : Weight K H L :=
        ⟨((i : H →ₗ[K] K) - (j : H →ₗ[K] K)), hn⟩
      have hα : α.IsNonZero := by
        intro hz
        apply hij
        apply Subtype.ext
        apply (rootSystem H).root.injective
        apply sub_eq_zero.mp
        apply DFunLike.ext
        intro x
        exact congr_fun hz x
      let k : H.root := ⟨α, by simpa [LieSubalgebra.root] using hα⟩
      apply b.sub_notMem_range_root i.property j.property
      refine ⟨k, ?_⟩
      apply DFunLike.ext
      intro x
      rfl
    have hm := lie_mem_genWeightSpace_of_mem_genWeightSpace (he i) (hf j)
    have hm' :
        ⁅e i, f j⁆ ∈
          rootSpace H ((i : H →ₗ[K] K) - (j : H →ₗ[K] K)) := by
      change ⁅e i, f j⁆ ∈
        rootSpace H (⇑(i : H →ₗ[K] K) - ⇑(j : H →ₗ[K] K))
      simpa only [sub_eq_add_neg] using hm
    have hz : ⁅e i, f j⁆ ∈ (⊥ : LieSubmodule K H L) := hbot ▸ hm'
    simpa using hz
  let B : Basis b.support H := {
    A := b.cartanMatrix
    h := fun i ↦ (rootSystem H).coroot i
    e := e
    f := f
    cartan_eq_lieSpan := cartan_eq_lieSpan b
    span_ef := lieSpan_range_union_eq_top_of_mem_rootSpace b e f ht he hf
    linInd := hlin
    nondegen := b.cartanMatrix_nondegenerate
    sl2 := ht
    lie_h_h := hhh
    lie_h_e := hhe
    lie_h_f := hhf
    lie_e_f_ne := hef
  }
  exact ⟨B, rfl, fun _ ↦ rfl⟩
