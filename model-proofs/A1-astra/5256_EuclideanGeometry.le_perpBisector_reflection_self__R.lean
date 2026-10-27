/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     EuclideanGeometry.le_perpBisector_reflection_self
Source:      Mathlib @ a02a63c2, Mathlib/Geometry/Euclidean/Projection.lean, line 591
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  A1-astra, arm R, verified in round 0 (round 0 = first attempt)
Prover:      gpt-6-astra
Setup:       GPT-6 Astra (Codex, effort medium): R = proof plus up to 3 repair rounds with Lean errors; RS = R plus lemma layer; RT = R with read-only Mathlib sources to search; N0-N3 = independent attempts
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
  rw [direction_perpBisector]
  infer_instance
