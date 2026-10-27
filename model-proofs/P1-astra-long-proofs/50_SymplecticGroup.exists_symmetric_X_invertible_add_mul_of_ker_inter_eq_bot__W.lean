/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     SymplecticGroup.exists_symmetric_X_invertible_add_mul_of_ker_inter_eq_bot
Source:      Mathlib @ d0a050ad6, Mathlib/LinearAlgebra/SymplecticGroup.lean, line 255
             (added after the model's training data; human proof 48 tactic steps)
Experiment:  P1-astra-long-proofs, arm W, solved after 4 call(s)
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
  let K := LinearMap.ker (Matrix.toLin' A)
  let b := Module.finBasis R K
  let f : K →ₗ[R] (l → R) := (Matrix.toLin' C).comp K.subtype
  have hf : Function.Injective f := by { intro x y h; have hxA : A *ᵥ (x : l → R) = 0 := x.property; have hyA : A *ᵥ (y : l → R) = 0 := y.property; have hzA : A • ((x : l → R) - (y : l → R)) = 0 := by { change A *ᵥ ((x : l → R) - (y : l → R)) = 0; rw [Matrix.mulVec_sub, hxA, hyA, sub_self] }; have hzC : C • ((x : l → R) - (y : l → R)) = 0 := by { change C *ᵥ ((x : l → R) - (y : l → R)) = 0; rw [Matrix.mulVec_sub]; exact sub_eq_zero.mpr h }; exact Subtype.ext (sub_eq_zero.mp (hker _ hzA hzC)) }
  obtain ⟨g, hg⟩ := LinearMap.exists_leftInverse_of_injective (f := f) (LinearMap.ker_eq_bot.mpr hf)
  have hleft : ∀ x, g (f x) = x := by simpa only [LinearMap.ext_iff, LinearMap.comp_apply, LinearMap.id_apply] using hg
  let T : Matrix (Fin (Module.finrank R K)) l R := Matrix.toLin'.symm (b.equivFun.toLinearMap.comp g)
  let V : Matrix l (Fin (Module.finrank R K)) R := Matrix.toLin'.symm (K.subtype.comp b.equivFun.symm.toLinearMap)
  have hT : Matrix.toLin' T = b.equivFun.toLinearMap.comp g := Matrix.toLin'.apply_symm_apply _
  have hV : Matrix.toLin' V = K.subtype.comp b.equivFun.symm.toLinearMap := Matrix.toLin'.apply_symm_apply _
  have hAV : A * V = 0 := by { apply Matrix.toLin'.injective; apply LinearMap.ext; intro x; change (A * V) *ᵥ x = (0 : Matrix l (Fin (Module.finrank R K)) R) *ᵥ x; rw [← Matrix.mulVec_mulVec, Matrix.zero_mulVec]; change A *ᵥ ((Matrix.toLin' V) x) = 0; rw [hV]; exact (b.equivFun.symm x).property }
  have hTCV : T * (C * V) = 1 := by { apply Matrix.toLin'.injective; apply LinearMap.ext; intro x; change (T * (C * V)) *ᵥ x = (1 : Matrix (Fin (Module.finrank R K)) (Fin (Module.finrank R K)) R) *ᵥ x; rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.one_mulVec]; change (Matrix.toLin' T) (C *ᵥ ((Matrix.toLin' V) x)) = x; rw [hT, hV]; change b.equivFun (g (f (b.equivFun.symm x))) = x; rw [hleft]; exact b.equivFun.apply_symm_apply x }
  have hWA : (C * V)ᵀ * A = 0 := by rw [Matrix.transpose_mul, Matrix.mul_assoc, ← hsymm, ← Matrix.mul_assoc, ← Matrix.transpose_mul, hAV, Matrix.transpose_zero, Matrix.zero_mul]
  let M := A + Tᵀ * T * C
  have hWM : (C * V)ᵀ * M = T * C := by { dsimp [M]; rw [Matrix.mul_add, hWA, zero_add, ← Matrix.mul_assoc, ← Matrix.mul_assoc, ← Matrix.transpose_mul, hTCV, Matrix.transpose_one, Matrix.one_mul] }
  have hzero : ∀ x, M *ᵥ x = 0 → x = 0 := by { intro x hx; have hTCx : (T * C) *ᵥ x = 0 := by { rw [← hWM, ← Matrix.mulVec_mulVec, hx, Matrix.mulVec_zero] }; have ht : T *ᵥ (C *ᵥ x) = 0 := by { simpa only [Matrix.mulVec_mulVec] using hTCx }; have hAx : A *ᵥ x = 0 := by { simpa only [M, Matrix.add_mulVec, ← Matrix.mulVec_mulVec, ht, Matrix.mulVec_zero, add_zero] using hx }; let y : K := ⟨x, hAx⟩; have hy : b.equivFun y = 0 := by { have ht' : (Matrix.toLin' T) (C *ᵥ x) = 0 := ht; rw [hT] at ht'; change b.equivFun (g (f y)) = 0 at ht'; simpa only [hleft] using ht' }; have hy0 : y = 0 := b.equivFun.injective (by simpa using hy); exact congrArg (fun z : K => (z : l → R)) hy0 }
  have hMinj : Function.Injective (Matrix.toLin' M) := by { intro x y h; apply sub_eq_zero.mp; apply hzero; rw [Matrix.mulVec_sub]; exact sub_eq_zero.mpr h }
  obtain ⟨q, hq⟩ := LinearMap.exists_leftInverse_of_injective (f := Matrix.toLin' M) (LinearMap.ker_eq_bot.mpr hMinj)
  have hqleft : ∀ x, q ((Matrix.toLin' M) x) = x := by simpa only [LinearMap.ext_iff, LinearMap.comp_apply, LinearMap.id_apply] using hq
  let N : Matrix l l R := Matrix.toLin'.symm q
  have hN : Matrix.toLin' N = q := Matrix.toLin'.apply_symm_apply _
  have hNM : N * M = 1 := by { apply Matrix.toLin'.injective; apply LinearMap.ext; intro x; change (N * M) *ᵥ x = (1 : Matrix l l R) *ᵥ x; rw [← Matrix.mulVec_mulVec, Matrix.one_mulVec]; change (Matrix.toLin' N) ((Matrix.toLin' M) x) = x; rw [hN]; exact hqleft x }
  have hdet : IsUnit M.det := by { apply isUnit_iff_exists_inv.mpr; refine ⟨N.det, ?_⟩; rw [mul_comm, ← Matrix.det_mul, hNM, Matrix.det_one] }
  have hMN : M * N = 1 := by { have h := Matrix.mul_nonsing_inv_cancel_left M (1 : Matrix l l R) hdet; simpa only [Matrix.mul_one, Matrix.inv_eq_left_inv hNM] using h }
  refine ⟨Tᵀ * T, by { change (Tᵀ * T)ᵀ = Tᵀ * T; rw [Matrix.transpose_mul, Matrix.transpose_transpose] }, ?_⟩
  change IsUnit M
  exact ⟨⟨M, N, hMN, hNM⟩, rfl⟩
