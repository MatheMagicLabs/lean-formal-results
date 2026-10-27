/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     Matrix.C_det_mul_charpoly_of_mul_eq_mul
Source:      Mathlib @ a02a63c2, Mathlib/LinearAlgebra/Matrix/Charpoly/Basic.lean, line 301
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  A1-astra, arm R, verified in round 2 (round 0 = first attempt)
Prover:      gpt-6-astra
Setup:       GPT-6 Astra (Codex, effort medium): R = proof plus up to 3 repair rounds with Lean errors; RS = R plus lemma layer; RT = R with read-only Mathlib sources to search; N0-N3 = independent attempts
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
  classical
  have h' :
      C.mapMatrix A * C.mapMatrix P =
        C.mapMatrix P * C.mapMatrix B := by
    apply Matrix.ext
    intro i j
    change (∑ k, C (A i k) * C (P k j)) =
      ∑ k, C (P i k) * C (B k j)
    simpa only [Matrix.mul_apply, map_sum, map_mul] using
      congrArg (C : R →+* R[X]) (congrFun (congrFun h i) j)
  have hs (Q : Matrix n n R[X]) :
      Matrix.scalar n X * Q = Q * Matrix.scalar n X := by
    apply Matrix.ext
    intro i j
    simp [Matrix.scalar, Matrix.diagonal, Matrix.mul_apply, mul_comm]
  have hc :
      A.charmatrix * C.mapMatrix P =
        C.mapMatrix P * B.charmatrix := by
    dsimp only [Matrix.charmatrix]
    rw [sub_mul, mul_sub, h', hs]
  change C P.det * A.charmatrix.det = C P.det * B.charmatrix.det
  simpa only [Matrix.det_mul, ← RingHom.map_det, mul_comm] using
    congrArg Matrix.det hc
