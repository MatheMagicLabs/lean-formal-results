/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     Matrix.linearIndependent_row_iff_isUnit
Source:      Mathlib @ a02a63c2, Mathlib/LinearAlgebra/Matrix/NonsingularInverse.lean, line 363
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  O2-repair-vs-resample, arm A, attempt 0, verified in round 0 (round 0 = first attempt)
Prover:      claude-opus-5-5
Setup:       Opus 5.5: arm B = one attempt plus up to 3 repair rounds with Lean error messages; arm A = 4 independent attempts (attempt k)
Check:       the proof replaced the human proof in the Mathlib file above; Lean reported
             0 errors and no `sorry`; sorry/admit/native_decide/search tactics were rejected.
-/

-- (context: the Mathlib file above this declaration)
theorem linearIndependent_row_iff_isUnit {R : Type*} [Ring R] [IsArtinianRing R]
    {A : Matrix m m R} : LinearIndependent R A.row ↔ IsUnit A := by
  let F : Matrix m m R → (m → R) →ₗ[R] (m → R) := fun M =>
    { toFun := M.vecMul
      map_add' := fun x y => Matrix.add_vecMul _ _ _
      map_smul' := fun r x => by
        ext j
        simp [Matrix.vecMul, dotProduct, Finset.mul_sum, mul_assoc] }
  have hsum : ∀ (M : Matrix m m R) (v : m → R), v ᵥ* M = ∑ i, v i • M.row i := by
    intro M v
    ext j
    simp [Matrix.vecMul, dotProduct, Finset.sum_apply, Matrix.row]
  have key : ∀ M : Matrix m m R, Function.Injective M.vecMul → ∃ N : Matrix m m R, N * M = 1 := by
    intro M hM
    have := IsArtinian.bijective_of_injective_endomorphism (F M) hM
    exact vecMul_surjective_iff_exists_left_inverse.mp this.2
  constructor
  · intro h
    have hinj : Function.Injective A.vecMul := by
      intro x y hxy
      have := Fintype.linearIndependent_iff.mp h (x - y) (by
        rw [← hsum]
        exact (map_sub (F A) x y).trans (sub_eq_zero.mpr hxy))
      ext i
      exact sub_eq_zero.mp (this i)
    obtain ⟨B, hBA⟩ := key A hinj
    have hBinj : Function.Injective B.vecMul := by
      intro x y hxy
      have := congrArg (· ᵥ* A) hxy
      simpa [Matrix.vecMul_vecMul, hBA] using this
    obtain ⟨C, hCB⟩ := key B hBinj
    have hCA : C = A := by
      calc C = C * (B * A) := by rw [hBA, Matrix.mul_one]
        _ = (C * B) * A := (Matrix.mul_assoc _ _ _).symm
        _ = A := by rw [hCB, Matrix.one_mul]
    have hAB : A * B = 1 := by
      rw [← hCA]
      exact hCB
    exact ⟨⟨A, B, hAB, hBA⟩, rfl⟩
  · intro h
    obtain ⟨B, hB⟩ : ∃ B : Matrix m m R, A * B = 1 := ⟨_, h.mul_val_inv⟩
    rw [Fintype.linearIndependent_iff]
    intro g hg
    have h0 : g ᵥ* A = 0 := by
      rw [hsum]
      exact hg
    have hg0 : g = 0 := by
      have := congrArg (· ᵥ* B) h0
      simpa [Matrix.vecMul_vecMul, hB] using this
    intro i
    simp [hg0]
