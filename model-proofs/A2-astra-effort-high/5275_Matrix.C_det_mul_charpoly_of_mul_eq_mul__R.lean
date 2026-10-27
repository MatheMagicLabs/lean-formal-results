/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     Matrix.C_det_mul_charpoly_of_mul_eq_mul
Source:      Mathlib @ a02a63c2, Mathlib/LinearAlgebra/Matrix/Charpoly/Basic.lean, line 301
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  A2-astra-effort-high, arm R, verified in round 2 (round 0 = first attempt)
Prover:      gpt-6-astra
Setup:       GPT-6 Astra, reasoning effort high (arms R, N0)
Check:       the proof replaced the human proof in the Mathlib file above; Lean reported
             0 errors and no `sorry`; sorry/admit/native_decide/search tactics were rejected.
-/

noncomputable section
universe u v w
namespace Matrix
open Finset Matrix Polynomial
variable {R S : Type*} [CommRing R] [CommRing S]
variable {m n : Type*} [DecidableEq m] [DecidableEq n] [Fintype m] [Fintype n]
variable (M₁₁ : Matrix m m R) (M₁₂ : Matrix m n R) (M₂₁ : Matrix n m R) (M₂₂ M : Matrix n n R)
variable (i j : n)
set_option backward.defeqAttrib.useBackward true in

theorem C_det_mul_charpoly_of_mul_eq_mul {A B P : Matrix n n R} (h : A * P = P * B) :
    C P.det * A.charpoly = C P.det * B.charpoly := by
  have hC :
      A.map (C : R →+* R[X]) * P.map C =
        P.map C * B.map C := by
    apply Matrix.ext
    intro i j
    simpa only [Matrix.mul_apply, Matrix.map_apply, map_sum, map_mul] using
      congrArg (fun Q : Matrix n n R => C (Q i j)) h
  have hs :
      scalar n (X : R[X]) * P.map C =
        P.map C * scalar n X := by
    apply Matrix.ext
    intro i j
    change
      (∑ k, (if i = k then (X : R[X]) else 0) * C (P k j)) =
        ∑ k, C (P i k) * (if k = j then X else 0)
    simp only [ite_mul, mul_ite, zero_mul, mul_zero,
      Finset.sum_ite_eq', Finset.sum_ite_eq, Finset.mem_univ, if_true]
    exact mul_comm _ _
  have hp :
      A.charmatrix * P.map C = P.map C * B.charmatrix := by
    change
      (scalar n X - A.map C) * P.map C =
        P.map C * (scalar n X - B.map C)
    rw [sub_mul, mul_sub, hC, hs]
  have hd : (P.map (C : R →+* R[X])).det = C P.det :=
    (RingHom.map_det (C : R →+* R[X]) P).symm
  simpa only [Matrix.det_mul, hd, Matrix.charpoly, mul_comm] using
    congrArg Matrix.det hp
