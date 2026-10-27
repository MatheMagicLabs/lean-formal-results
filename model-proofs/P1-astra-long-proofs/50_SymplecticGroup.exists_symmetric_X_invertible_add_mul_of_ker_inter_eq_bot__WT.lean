/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     SymplecticGroup.exists_symmetric_X_invertible_add_mul_of_ker_inter_eq_bot
Source:      Mathlib @ d0a050ad6, Mathlib/LinearAlgebra/SymplecticGroup.lean, line 255
             (added after the model's training data; human proof 48 tactic steps)
Experiment:  P1-astra-long-proofs, arm WT, solved after 3 call(s)
Prover:      gpt-6-astra
Setup:       GPT-6 Astra (Codex, effort medium), at most 10 calls per theorem: W = whole proof plus repair rounds;
             WT = W with read-only Mathlib sources to search; P = Lean-checked skeleton of have-steps, then one step per call
Check:       the proof replaced the human proof in the Mathlib file above; Lean reported
             0 errors and no `sorry`.
-/

private lemma exists_symmetric_X_invertible_add_mul_of_ker_inter_eq_bot {R : Type*} [Field R]
    {A C : Matrix l l R} (hker : ∀ (x : l → R), (A • x = 0) → (C • x = 0) → x = 0)
    (hsymm : Aᵀ * C = Cᵀ * A) :
    ∃ (X : Matrix l l R), X.IsSymm ∧ IsUnit (A + X * C) := by
  classical
  obtain ⟨V, U, e, hV, hU, hn⟩ := A.exists_rank_normal_form
  obtain ⟨v, rfl⟩ := hV
  obtain ⟨u, rfl⟩ := hU
  let V : Matrix l l R := ↑v
  let U : Matrix l l R := ↑u
  let W : Matrix l l R := ↑v⁻¹
  let P := V * A * U
  let B := Wᵀ * C * U
  let Q := 1 - P
  have hWV : W * V = 1 := by simp [W, V]
  have hVW : V * W = 1 := by simp [W, V]
  have hT : Vᵀ * Wᵀ = 1 := by
    rw [← transpose_mul, hWV, transpose_one]
  have hP : P = (fromBlocks 1 0 0 0).submatrix e e := hn
  have hPs : Pᵀ = P := by
    rw [hP]
    change (fromBlocks 1 0 0 0)ᵀ.submatrix e e =
      (fromBlocks 1 0 0 0).submatrix e e
    simp [fromBlocks_transpose]
  have hPP : P * P = P := by
    rw [hP, submatrix_mul_equiv]
    simp [fromBlocks_multiply]
  have hQs : Qᵀ = Q := by
    simp [Q, transpose_sub, hPs]
  have hPB : P * B = Bᵀ * P := by
    calc
      P * B = Pᵀ * B := by rw [hPs]
      _ = Uᵀ * (Aᵀ * C) * U := by
        dsimp [P, B]
        simp only [transpose_mul, mul_assoc,
          ← mul_assoc Vᵀ Wᵀ, hT, one_mul]
      _ = Uᵀ * (Cᵀ * A) * U := by rw [hsymm]
      _ = Bᵀ * P := by
        dsimp [P, B]
        simp only [transpose_mul, transpose_transpose, mul_assoc,
          ← mul_assoc W V, hWV, one_mul]
  have hk : ∀ x : l → R, P • x = 0 → B • x = 0 → x = 0 := by
    intro x hx hy
    have ha : A • (U • x) = 0 := by
      apply (mulVec_injective_iff_isUnit.mpr v.isUnit)
      change V • (A • (U • x)) = V • 0
      simpa only [P, mul_smul, smul_zero] using hx
    have hWt : IsUnit Wᵀ := by
      simpa only [isUnit_transpose] using v⁻¹.isUnit
    have hc : C • (U • x) = 0 := by
      apply (mulVec_injective_iff_isUnit.mpr hWt)
      change Wᵀ • (C • (U • x)) = Wᵀ • 0
      simpa only [B, mul_smul, smul_zero] using hy
    have hz := hker (U • x) ha hc
    have hz' := congrArg (fun y : l → R =>
      (↑u⁻¹ : Matrix l l R) • y) hz
    simpa [U, ← mul_smul] using hz'
  have hPQzero : P * Q = 0 := by
    change P * (1 - P) = 0
    rw [mul_sub, mul_one, hPP, sub_self]
  have hPQ : P * (P + Q * B) = P := by
    rw [mul_add, ← mul_assoc P Q B, hPP, hPQzero, zero_mul, add_zero]
  have hz : ∀ x : l → R, (P + Q * B) • x = 0 → x = 0 := by
    intro x hx
    have hpx : P • x = 0 := by
      have ht := congrArg (fun y : l → R => P • y) hx
      simpa only [← mul_smul, hPQ, smul_zero] using ht
    have hqbx : Q • (B • x) = 0 := by
      simpa only [add_smul, mul_smul, hpx, zero_add] using hx
    have hpbx : P • (B • x) = 0 := by
      rw [← mul_smul, hPB, mul_smul, hpx, smul_zero]
    apply hk x hpx
    calc
      B • x = P • (B • x) + Q • (B • x) := by
        simp [Q, sub_smul]
      _ = 0 := by rw [hpbx, hqbx, add_zero]
  have ht : IsUnit (P + Q * B) := by
    apply mulVec_injective_iff_isUnit.mp
    intro x y hxy
    apply sub_eq_zero.mp
    apply hz
    change (P + Q * B) *ᵥ (x - y) = 0
    rw [mulVec_sub, hxy, sub_self]
  refine ⟨W * Q * Wᵀ, ?_, ?_⟩
  · change (W * Q * Wᵀ)ᵀ = W * Q * Wᵀ
    simp only [transpose_mul, transpose_transpose, hQs, mul_assoc]
  · have he : V * (A + (W * Q * Wᵀ) * C) * U = P + Q * B := by
      simp only [mul_add, add_mul]
      dsimp [P, B]
      simp only [mul_assoc, ← mul_assoc V W, hVW, one_mul]
    rw [isUnit_iff_isUnit_det, isUnit_iff_ne_zero] at ht ⊢
    intro h
    apply ht
    rw [← he, det_mul, det_mul, h, mul_zero, zero_mul]
