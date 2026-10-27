/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     Matrix.C_det_mul_charpoly_of_mul_eq_mul
Source:      Mathlib @ a02a63c2, Mathlib/LinearAlgebra/Matrix/Charpoly/Basic.lean, line 301
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  O3-lemma-layer, arm R, verified in round 1 (round 0 = first attempt)
Prover:      claude-opus-5-5
Setup:       Opus 5.5 with repair loop: arm R = repair only; arm RS = repair plus the Lean-checked lemma layer
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
  have h2 : A.map C * P.map C = P.map C * B.map C := by
    rw [← Matrix.map_mul, ← Matrix.map_mul, h]
  have hX : scalar n (X : R[X]) * P.map C = P.map C * scalar n X :=
    (scalar_commute (X : R[X]) (fun r => Commute.all X r) _).eq
  have h1 : charmatrix A * P.map C = P.map C * charmatrix B := by
    first
      | (simp only [charmatrix, sub_mul, mul_sub, RingHom.mapMatrix_apply]
         rw [hX, h2])
      | (ext i j
         have e1 := congrFun (congrFun h2 i) j
         have e2 := congrFun (congrFun hX i) j
         simp only [charmatrix, sub_mul, mul_sub, sub_apply, RingHom.mapMatrix_apply]
         rw [e1, e2])
  have h3 := congrArg det h1
  have hd : (P.map C).det = C P.det := by rw [RingHom.map_det]; rfl
  rw [det_mul, det_mul, hd] at h3
  rw [mul_comm (A.charmatrix.det)] at h3
  unfold charpoly
  exact h3
