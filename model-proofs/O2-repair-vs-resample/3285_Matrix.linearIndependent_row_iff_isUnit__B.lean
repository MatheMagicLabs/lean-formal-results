/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     Matrix.linearIndependent_row_iff_isUnit
Source:      Mathlib @ a02a63c2, Mathlib/LinearAlgebra/Matrix/NonsingularInverse.lean, line 363
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  O2-repair-vs-resample, arm B, verified in round 1 (round 0 = first attempt)
Prover:      claude-opus-5-5
Setup:       Opus 5.5: arm B = one attempt plus up to 3 repair rounds with Lean error messages; arm A = 4 independent attempts (attempt k)
Check:       the proof replaced the human proof in the Mathlib file above; Lean reported
             0 errors and no `sorry`; sorry/admit/native_decide/search tactics were rejected.
-/

-- (context: the Mathlib file above this declaration)
theorem linearIndependent_row_iff_isUnit {R : Type*} [Ring R] [IsArtinianRing R]
    {A : Matrix m m R} : LinearIndependent R A.row ↔ IsUnit A := by
  classical
  let f : (m → R) →ₗ[R] (m → R) :=
    { toFun := fun x => x ᵥ* A
      map_add' := fun x y => Matrix.add_vecMul A x y
      map_smul' := fun r x => by
        ext j
        simp [Matrix.vecMul, dotProduct, Finset.mul_sum, mul_assoc] }
  have hf : ∀ x, f x = x ᵥ* A := fun x => rfl
  have key : LinearIndependent R A.row ↔ Function.Injective f := by
    rw [Fintype.linearIndependent_iff, injective_iff_map_eq_zero]
    have this : ∀ g : m → R, ∑ i, g i • A.row i = f g := by
      intro g
      ext j
      simp [hf, Matrix.vecMul, dotProduct, Finset.sum_apply, Matrix.row]
    simp only [this]
    constructor
    · intro h g hg
      funext i
      exact h g hg i
    · intro h g hg i
      exact congrFun (h g hg) i
  rw [key]
  constructor
  · intro hinj
    have hsurj : Function.Surjective f :=
      IsArtinian.surjective_of_injective_endomorphism f hinj
    obtain ⟨B, hBA⟩ := vecMul_surjective_iff_exists_left_inverse.mp hsurj
    have hAB : A * B = 1 := by
      have h2 : (A * B) * A = 1 * A := by
        rw [Matrix.mul_assoc, hBA, Matrix.mul_one, Matrix.one_mul]
      ext i j
      have h1 : f ((A * B) i) = f ((1 : Matrix m m R) i) := congrFun h2 i
      exact congrFun (hinj h1) j
    exact ⟨⟨A, B, hAB, hBA⟩, rfl⟩
  · rintro ⟨u, rfl⟩
    intro x y hxy
    have := congrArg (fun z => z ᵥ* (↑u⁻¹ : Matrix m m R)) hxy
    simpa [hf, Matrix.vecMul_vecMul] using this
