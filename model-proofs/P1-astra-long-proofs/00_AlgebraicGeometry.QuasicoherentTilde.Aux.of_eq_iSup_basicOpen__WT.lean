/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     AlgebraicGeometry.QuasicoherentTilde.Aux.of_eq_iSup_basicOpen
Source:      Mathlib @ d0a050ad6, Mathlib/AlgebraicGeometry/Modules/Tilde.lean, line 660
             (added after the model's training data; human proof 81 tactic steps)
Experiment:  P1-astra-long-proofs, arm WT, solved after 3 call(s)
Prover:      gpt-6-astra
Setup:       GPT-6 Astra (Codex, effort medium), at most 10 calls per theorem: W = whole proof plus repair rounds;
             WT = W with read-only Mathlib sources to search; P = Lean-checked skeleton of have-steps, then one step per call
Check:       the proof replaced the human proof in the Mathlib file above; Lean reported
             0 errors and no `sorry`.
-/

private lemma Aux.of_eq_iSup_basicOpen {M : (Spec R).Modules} (V : (Spec R).Opens)
    {ι : Type*} [Finite ι] (g : ι → R) (hg : V = ⨆ i, basicOpen (g i))
    (h₁ : ∀ (i : ι), Aux M (basicOpen (g i))) :
    Aux M V := by
  set_option backward.isDefEq.respectTransparency.types false in
  classical
  let ρ {U W : (Spec R).Opens} (h : U ≤ W) :
      Γ(M, W) →ₗ[R] Γ(M, U) :=
    ((modulesSpecToSheaf.obj M).obj.map (homOfLE h).op).hom
  have hc {U W Z : (Spec R).Opens} (h : U ≤ W) (k : W ≤ Z)
      (s : Γ(M, Z)) : ρ h (ρ k s) = ρ (h.trans k) s := by
    change M.presheaf.map (homOfLE h).op
      (M.presheaf.map (homOfLE k).op s) =
      M.presheaf.map (homOfLE (h.trans k)).op s
    simp [← M.presheaf.map_comp_apply, ← op_comp, homOfLE_comp]
  have kill {U : (Spec R).Opens} {f : R} {n N : ℕ}
      (hn : n ≤ N) {t : Γ(M, U)} (ht : f ^ n • t = 0) :
      f ^ N • t = 0 := by
    rw [← Nat.sub_add_cancel hn, pow_add, mul_smul, ht, smul_zero]
  have hu (a : R) (ha : Aux M (basicOpen a)) (f : R)
      (t : Γ(M, basicOpen a))
      (ht : ρ (inf_le_left : basicOpen a ⊓ basicOpen f ≤ basicOpen a) t = 0) :
      ∃ n : ℕ, f ^ n • t = 0 := by
    have h := ha.uniqueness (a * f)
    rw [basicOpen_mul] at h
    obtain ⟨n, hn⟩ := h inf_le_left t ht
    refine ⟨n, ?_⟩
    apply ((M.isSMulRegular_of_le_basicOpen
      (U := basicOpen a) le_rfl).pow n).right_eq_zero_of_smul
    simpa only [mul_pow, mul_smul] using hn
  have he (a : R) (ha : Aux M (basicOpen a)) (f : R)
      (s : Γ(M, basicOpen a ⊓ basicOpen f)) :
      ∃ (n : ℕ) (t : Γ(M, basicOpen a)),
      ρ (inf_le_left : basicOpen a ⊓ basicOpen f ≤ basicOpen a) t =
      f ^ n • s := by
    have h := ha.existence (a * f)
    rw [basicOpen_mul] at h
    obtain ⟨n, t, ht⟩ := h inf_le_left s
    have hunit := (M.isUnit_algebraMap_end_of_le_basicOpen
      (U := basicOpen a) a le_rfl).pow n
    rw [← map_pow, Module.End.isUnit_iff] at hunit
    obtain ⟨t', ht'⟩ := hunit.surjective t
    change a ^ n • t' = t at ht'
    refine ⟨n, t', ?_⟩
    apply (M.isSMulRegular_of_le_basicOpen
      (U := basicOpen a ⊓ basicOpen f) inf_le_left).pow n
    calc
      a ^ n • ρ inf_le_left t' = ρ inf_le_left (a ^ n • t') :=
        (map_smul _ _ _).symm
      _ = (a * f) ^ n • s := by
        rw [ht']
        exact ht
      _ = a ^ n • (f ^ n • s) := by rw [mul_pow, mul_smul]
  let F : TopCat.Sheaf Ab (Spec R) := ⟨M.presheaf, M.isSheaf⟩
  have hle (i : ι) : basicOpen (g i) ≤ V := by
    rw [hg]
    exact le_iSup (fun i ↦ basicOpen (g i)) i
  refine ⟨?_, ?_⟩
  · intro f hf s
    have hex (i : ι) :
        ∃ (n : ℕ) (t : Γ(M, basicOpen (g i))),
        ρ (inf_le_left : basicOpen (g i) ⊓ basicOpen f ≤ basicOpen (g i)) t =
        f ^ n • ρ (inf_le_right : basicOpen (g i) ⊓ basicOpen f ≤ basicOpen f) s :=
      he (g i) (h₁ i) f (ρ inf_le_right s)
    choose n t ht using hex
    obtain ⟨N, hN⟩ := Finite.exists_le n
    let t' (i : ι) : Γ(M, basicOpen (g i)) := f ^ (N - n i) • t i
    have ht' (i : ι) :
        ρ (inf_le_left : basicOpen (g i) ⊓ basicOpen f ≤ basicOpen (g i)) (t' i) =
        f ^ N • ρ (inf_le_right : basicOpen (g i) ⊓ basicOpen f ≤ basicOpen f) s := by
      dsimp [t']
      rw [map_smul, ht i, ← mul_smul, ← pow_add, Nat.sub_add_cancel (hN i)]
    let d (i j : ι) : Γ(M, basicOpen (g i) ⊓ basicOpen (g j)) :=
      ρ inf_le_left (t' i) - ρ inf_le_right (t' j)
    have hd (i j : ι) : ∃ m : ℕ, f ^ m • d i j = 0 := by
      have hz :
          ρ (inf_le_left :
            (basicOpen (g i) ⊓ basicOpen (g j)) ⊓ basicOpen f ≤
            basicOpen (g i) ⊓ basicOpen (g j)) (d i j) = 0 := by
        have hi := congrArg
          (ρ (show (basicOpen (g i) ⊓ basicOpen (g j)) ⊓ basicOpen f ≤
            basicOpen (g i) ⊓ basicOpen f from
            inf_le_inf inf_le_left le_rfl)) (ht' i)
        have hj := congrArg
          (ρ (show (basicOpen (g i) ⊓ basicOpen (g j)) ⊓ basicOpen f ≤
            basicOpen (g j) ⊓ basicOpen f from
            inf_le_inf inf_le_right le_rfl)) (ht' j)
        simp only [hc, map_smul] at hi hj
        dsimp [d]
        rw [map_sub, hc, hc]
        exact sub_eq_zero.mpr (hi.trans hj.symm)
      have h := hu (g i * g j)
        ((h₁ i).of_le (g i * g j) (basicOpen_mul_le_left _ _)) f
      rw [basicOpen_mul] at h
      exact h (d i j) hz
    choose m hm using hd
    obtain ⟨K, hK⟩ := Finite.exists_le (fun p : ι × ι ↦ m p.1 p.2)
    have hcompat : TopCat.Presheaf.IsCompatible M.presheaf
        (fun i ↦ basicOpen (g i)) (fun i ↦ f ^ K • t' i) := by
      intro i j
      change ρ inf_le_left (f ^ K • t' i) = ρ inf_le_right (f ^ K • t' j)
      rw [(ρ (inf_le_left :
        basicOpen (g i) ⊓ basicOpen (g j) ≤ basicOpen (g i))).map_smul
          (f ^ K) (t' i)]
      rw [(ρ (inf_le_right :
        basicOpen (g i) ⊓ basicOpen (g j) ≤ basicOpen (g j))).map_smul
          (f ^ K) (t' j)]
      apply sub_eq_zero.mp
      rw [← smul_sub]
      exact kill (hK (i, j)) (hm i j)
    obtain ⟨t₀, ht₀, -⟩ := F.existsUnique_gluing'
      (fun i ↦ basicOpen (g i)) V (fun i ↦ homOfLE (hle i))
      (le_of_eq hg) (fun i ↦ f ^ K • t' i) hcompat
    refine ⟨K + N, t₀, ?_⟩
    have hcover : basicOpen f ≤ ⨆ i, basicOpen (g i) ⊓ basicOpen f := by
      rw [← iSup_inf_eq, ← hg, inf_eq_right.mpr hf]
    apply F.eq_of_locally_eq' (fun i ↦ basicOpen (g i) ⊓ basicOpen f)
      (basicOpen f) (fun i ↦ homOfLE inf_le_right) hcover
    intro i
    change ρ inf_le_right (ρ hf t₀) =
      ρ inf_le_right (f ^ (K + N) • s)
    rw [hc, map_smul]
    have h := congrArg
      (ρ (inf_le_left : basicOpen (g i) ⊓ basicOpen f ≤ basicOpen (g i))) (ht₀ i)
    change ρ inf_le_left (ρ (hle i) t₀) =
      ρ inf_le_left (f ^ K • t' i) at h
    rw [hc, map_smul, ht' i] at h
    simpa only [pow_add, mul_smul] using h
  · intro f hf t ht
    change ρ hf t = 0 at ht
    have hex (i : ι) : ∃ n : ℕ, f ^ n • ρ (hle i) t = 0 := by
      apply hu (g i) (h₁ i) f
      have h := congrArg
        (ρ (inf_le_right : basicOpen (g i) ⊓ basicOpen f ≤ basicOpen f)) ht
      simpa only [hc, map_zero] using h
    choose n hn using hex
    obtain ⟨N, hN⟩ := Finite.exists_le n
    refine ⟨N, ?_⟩
    apply F.eq_of_locally_eq' (fun i ↦ basicOpen (g i)) V
      (fun i ↦ homOfLE (hle i)) (le_of_eq hg)
    intro i
    change ρ (hle i) (f ^ N • t) = ρ (hle i) 0
    rw [map_smul, map_zero]
    exact kill (hN i) (hn i)
