/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     Matrix.C_det_mul_charpoly_of_mul_eq_mul
Source:      Mathlib @ a02a63c2, Mathlib/LinearAlgebra/Matrix/Charpoly/Basic.lean, line 301
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  E1-repair-decomposition, arm V, verified in round 2 (round 0 = first attempt)
Prover:      gpt-6-astra
Setup:       GPT-6 Astra, which part of Lean feedback makes repair work: after a shared first attempt (E0), V = full error messages, Z = line numbers only, B = only "Lean rejected this proof"
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
  let f : R →+* R[X] := C
  have hmap : A.map f * P.map f = P.map f * B.map f := by
    apply Matrix.ext
    intro a b
    change (∑ k, f (A a k) * f (P k b)) =
      ∑ k, f (P a k) * f (B k b)
    simpa only [Matrix.mul_apply, map_sum, map_mul] using
      congrArg (fun Q : Matrix n n R => f (Q a b)) h
  have hX :
      (scalar n (X : R[X]) - A.map f) * P.map f =
        P.map f * (scalar n (X : R[X]) - B.map f) := by
    rw [sub_mul, mul_sub, hmap]
    congr 1
    apply Matrix.ext
    intro a b
    simp [Matrix.mul_apply, Matrix.scalar, Matrix.diagonal,
      ite_mul, mul_ite, mul_comm]
  have hdet : (P.map f).det = C P.det := by
    simp [f, Matrix.det_apply]
  change C P.det * (scalar n (X : R[X]) - A.map f).det =
    C P.det * (scalar n (X : R[X]) - B.map f).det
  simpa only [Matrix.det_mul, hdet, mul_comm] using
    congrArg Matrix.det hX
