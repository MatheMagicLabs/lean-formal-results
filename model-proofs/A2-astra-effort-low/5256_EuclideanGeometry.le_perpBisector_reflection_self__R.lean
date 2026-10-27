/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     EuclideanGeometry.le_perpBisector_reflection_self
Source:      Mathlib @ a02a63c2, Mathlib/Geometry/Euclidean/Projection.lean, line 591
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  A2-astra-effort-low, arm R, verified in round 2 (round 0 = first attempt)
Prover:      gpt-6-astra
Setup:       GPT-6 Astra, reasoning effort low (arms R, N0)
Check:       the proof replaced the human proof in the Mathlib file above; Lean reported
             0 errors and no `sorry`; sorry/admit/native_decide/search tactics were rejected.
-/

noncomputable section
namespace EuclideanGeometry
variable {𝕜 : Type*} {V : Type*} {P : Type*} [RCLike 𝕜]
variable [NormedAddCommGroup V] [InnerProductSpace 𝕜 V]
variable {V₂ P₂ : Type*} [NormedAddCommGroup V₂] [InnerProductSpace 𝕜 V₂]
open AffineSubspace
variable [MetricSpace P] [NormedAddTorsor V P]
variable [MetricSpace P₂] [NormedAddTorsor V₂ P₂]
section perpBisector
variable {V P : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MetricSpace P]

theorem le_perpBisector_reflection_self (s : AffineSubspace ℝ P) [Nonempty s]
    [s.direction.HasOrthogonalProjection] (a : P) :
    s ≤ perpBisector (reflection s a) a :=
  perpBisector_comm (reflection s a) a ▸ le_perpBisector_self_reflection s a

instance (a b : P) : (perpBisector a b).direction.HasOrthogonalProjection := by
  unfold perpBisector
  rw [direction_mk']
  have h : ((innerₛₗ ℝ) (b -ᵥ a)).ker = (ℝ ∙ (b -ᵥ a))ᗮ := by
    ext x
    rw [Submodule.mem_orthogonal]
    constructor
    · intro hx y hy
      change inner ℝ (b -ᵥ a) x = 0 at hx
      obtain ⟨r, rfl⟩ := Submodule.mem_span_singleton.mp hy
      simp [inner_smul_left, inner_smul_right, hx,
        real_inner_comm x (b -ᵥ a)]
    · intro hx
      have hx' := hx (b -ᵥ a) (Submodule.subset_span (by simp))
      change inner ℝ (b -ᵥ a) x = 0
      simpa only [real_inner_comm] using hx'
  rw [h]
  infer_instance
