/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     CartanMatrix.Realisation.isIrreducible_toRootPairing
Source:      Mathlib @ d0a050ad6, Mathlib/LinearAlgebra/Matrix/Cartan/Realisation.lean, line 526
             (added after the model's training data; human proof 36 tactic steps)
Experiment:  P1-astra-long-proofs, arm W, solved after 7 call(s)
Prover:      gpt-6-astra
Setup:       GPT-6 Astra (Codex, effort medium), at most 10 calls per theorem: W = whole proof plus repair rounds;
             WT = W with read-only Mathlib sources to search; P = Lean-checked skeleton of have-steps, then one step per call
Check:       the proof replaced the human proof in the Mathlib file above; Lean reported
             0 errors and no `sorry`.
-/

lemma isIrreducible_toRootPairing [Nonempty n] {k V W : Type*} [Field k] [CharZero k]
    [AddCommGroup V] [Module k V] [AddCommGroup W] [Module k W] (rl : Realisation n k V W)
    (hr : span k (range rl.sRoot) = ⊤)
    (hA' : rl.matrix.IsIndecomposable) :
    rl.toRootPairing.IsIrreducible := by
  classical
  let s : n → rl.idx := fun i ↦ ⟨_, rl.sPair_mem_idx i⟩
  have hcut (t : Set n)
      (ht : ∀ i ∉ t, ∀ j ∈ t, rl.matrix i j = 0) :
      t = ∅ ∨ t = univ := by
    let e : Fin (Fintype.card ↥t) ⊕ Fin (Fintype.card ↥(tᶜ)) ≃ n :=
      (Equiv.sumCongr (Fintype.equivFin ↥t).symm
        (Fintype.equivFin ↥(tᶜ)).symm).trans (Equiv.sumCompl (fun i ↦ i ∈ t))
    have hl (i : Fin (Fintype.card ↥t)) : e (Sum.inl i) ∈ t :=
      ((Fintype.equivFin ↥t).symm i).property
    have hr' (i : Fin (Fintype.card ↥(tᶜ))) : e (Sum.inr i) ∉ t :=
      ((Fintype.equivFin ↥(tᶜ)).symm i).property
    let A := rl.matrix.submatrix (fun i ↦ e (Sum.inl i)) (fun i ↦ e (Sum.inl i))
    let B := rl.matrix.submatrix (fun i ↦ e (Sum.inl i)) (fun i ↦ e (Sum.inr i))
    let D := rl.matrix.submatrix (fun i ↦ e (Sum.inr i)) (fun i ↦ e (Sum.inr i))
    have he : rl.matrix = (fromBlocks A B 0 D).submatrix e.symm e.symm := by
      ext i j
      obtain ⟨i, rfl⟩ := e.surjective i
      obtain ⟨j, rfl⟩ := e.surjective j
      cases i with
      | inl i =>
        cases j <;> simp [A, B, D, Matrix.submatrix]
      | inr i =>
        cases j with
        | inl j =>
          simpa [Matrix.submatrix] using ht _ (hr' i) _ (hl j)
        | inr j =>
          simp [A, B, D, Matrix.submatrix]
    unfold Matrix.IsIndecomposable at hA'
    rcases hA' _ _ A B D e he with h | h
    · left
      apply Set.eq_empty_iff_forall_notMem.mpr
      intro i hi
      have hp : 0 < Fintype.card ↥t :=
        Fintype.card_pos_iff.mpr ⟨⟨i, hi⟩⟩
      omega
    · right
      apply Set.eq_univ_iff_forall.mpr
      intro i
      by_contra hi
      have hp : 0 < Fintype.card ↥(tᶜ) :=
        Fintype.card_pos_iff.mpr ⟨⟨i, hi⟩⟩
      omega
  have hc : span k (range rl.sCoroot) = ⊤ := by
    let b : Basis n k V := Basis.mk rl.lin_ind_sRoot (by rw [hr])
    letI : Module.Finite k V := Module.Finite.of_basis b
    let e : W ≃ₗ[k] Module.Dual k V :=
      LinearEquiv.ofBijective rl.pairing.flip
        (LinearMap.IsPerfPair.bijective_left rl.pairing.flip)
    letI : Module.Finite k W :=
      Module.Finite.of_injective e.toLinearMap e.injective
    apply rl.flip.lin_ind_sRoot.span_eq_top_of_card_eq_finrank
    calc
      Fintype.card n = Module.finrank k (Module.Dual k V) :=
        (Module.finrank_eq_card_basis b.dualBasis).symm
      _ = Module.finrank k W := e.finrank_eq.symm
  have hmain (q : Submodule k V)
      (hq : ∀ i x, x ∈ q →
        x - rl.pairing x (rl.sCoroot i) • rl.sRoot i ∈ q) :
      q = ⊥ ∨ q = ⊤ := by
    have extract (i : n) (x : V) (hx : x ∈ q)
        (hc : rl.pairing x (rl.sCoroot i) ≠ 0) : rl.sRoot i ∈ q := by
      have hm : rl.pairing x (rl.sCoroot i) • rl.sRoot i ∈ q := by
        simpa only [sub_sub_cancel] using q.sub_mem hx (hq i x hx)
      have hm' := q.smul_mem (rl.pairing x (rl.sCoroot i))⁻¹ hm
      simpa [smul_smul, hc] using hm'
    let t : Set n := {i | rl.sRoot i ∉ q}
    have ht : ∀ i ∉ t, ∀ j ∈ t, rl.matrix i j = 0 := by
      intro i hi j hj
      by_contra hij
      have hi' : rl.sRoot i ∈ q := by simpa [t] using hi
      have hij' : rl.pairing (rl.sRoot i) (rl.sCoroot j) ≠ 0 := by
        simpa using hij
      exact hj (extract j (rl.sRoot i) hi' hij')
    rcases hcut t ht with ht | ht
    · right
      apply top_unique
      rw [← hr]
      apply Submodule.span_le.mpr
      rintro _ ⟨i, rfl⟩
      by_contra hi
      have hi' : i ∈ t := hi
      simpa [ht] using hi'
    · left
      apply le_antisymm ?_ bot_le
      intro x hx
      change x = 0
      have hsub : x - 0 ∈ span k (range rl.flip.sCoroot) := by
        change x - 0 ∈ span k (range rl.sRoot)
        rw [hr]
        trivial
      apply (rl.flip.eq_iff_forall_pairing_sRoot_eq hsub).mpr
      intro i
      change rl.pairing x (rl.sCoroot i) = rl.pairing 0 (rl.sCoroot i)
      have hz : rl.pairing x (rl.sCoroot i) = 0 := by
        by_contra hc
        have hi : i ∈ t := by simp [ht]
        exact hi (extract i x hx hc)
      simpa using hz
  let i : n := Classical.arbitrary n
  have hv : rl.sRoot i ≠ 0 := by
    intro h
    have hp := rl.pairing_fst_snd (rl.sPair_mem_idx i)
    norm_num [h] at hp
  have hw : rl.sCoroot i ≠ 0 := by
    intro h
    have hp := rl.pairing_fst_snd (rl.sPair_mem_idx i)
    norm_num [h] at hp
  haveI : Nontrivial V := ⟨⟨rl.sRoot i, 0, hv⟩⟩
  haveI : Nontrivial W := ⟨⟨rl.sCoroot i, 0, hw⟩⟩
  constructor
  · infer_instance
  · infer_instance
  · intro q hq hne
    have hinv : ∀ i x, x ∈ q →
        x - rl.pairing x (rl.sCoroot i) • rl.sRoot i ∈ q := by
      intro i x hx
      have hh : rl.toRootPairing.reflection (s i) x ∈ q := by
        apply hq (s i)
        exact hx
      simpa [RootPairing.reflection_apply, s] using hh
    exact (hmain q hinv).resolve_left hne
  · intro q hq hne
    have extract (i : n) (y : W) (hy : y ∈ q)
        (hp : rl.pairing (rl.sRoot i) y ≠ 0) : rl.sCoroot i ∈ q := by
      have hh : rl.toRootPairing.coreflection (s i) y ∈ q := by
        apply hq (s i)
        exact hy
      rw [RootPairing.coreflection_apply] at hh
      change y - rl.pairing (rl.sRoot i) y • rl.sCoroot i ∈ q at hh
      have hm : rl.pairing (rl.sRoot i) y • rl.sCoroot i ∈ q := by
        simpa only [sub_sub_cancel] using q.sub_mem hy hh
      have hm' := q.smul_mem (rl.pairing (rl.sRoot i) y)⁻¹ hm
      simpa [smul_smul, hp] using hm'
    let t : Set n := {i | rl.sCoroot i ∈ q}
    have ht : ∀ i ∉ t, ∀ j ∈ t, rl.matrix i j = 0 := by
      intro i hi j hj
      by_contra hij
      have hij' : rl.pairing (rl.sRoot i) (rl.sCoroot j) ≠ 0 := by
        simpa using hij
      exact hi (extract i (rl.sCoroot j) hj hij')
    rcases hcut t ht with ht | ht
    · exfalso
      apply hne
      apply le_antisymm ?_ bot_le
      intro y hy
      change y = 0
      have hsub : y - 0 ∈ span k (range rl.sCoroot) := by
        rw [hc]
        trivial
      apply (rl.eq_iff_forall_pairing_sRoot_eq hsub).mpr
      intro i
      have hz : rl.pairing (rl.sRoot i) y = 0 := by
        by_contra hp
        have hi : i ∈ t := extract i y hy hp
        simpa [ht] using hi
      simpa using hz
    · apply top_unique
      rw [← hc]
      apply Submodule.span_le.mpr
      rintro _ ⟨i, rfl⟩
      have hi : i ∈ t := by simp [ht]
      exact hi
