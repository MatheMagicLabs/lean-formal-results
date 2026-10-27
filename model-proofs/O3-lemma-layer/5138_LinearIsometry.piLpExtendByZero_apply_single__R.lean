/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     LinearIsometry.piLpExtendByZero_apply_single
Source:      Mathlib @ a02a63c2, Mathlib/Analysis/Normed/Lp/PiLp.lean, line 971
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  O3-lemma-layer, arm R, verified in round 0 (round 0 = first attempt)
Prover:      claude-opus-5-5
Setup:       Opus 5.5 with repair loop: arm R = repair only; arm RS = repair plus the Lean-checked lemma layer
Check:       the proof replaced the human proof in the Mathlib file above; Lean reported
             0 errors and no `sorry`; sorry/admit/native_decide/search tactics were rejected.
-/

open Module Real Set Filter Bornology NNReal ENNReal WithLp
open scoped Uniformity
noncomputable section
namespace PiLp
variable (p : ℝ≥0∞) (𝕜 : Type*) {ι : Type*} (α : ι → Type*) (β : ι → Type*)
section
variable {𝕜 p α}
variable [Semiring 𝕜] [∀ i, SeminormedAddCommGroup (β i)]
variable [∀ i, Module 𝕜 (β i)] (c : 𝕜)
variable (x y : PiLp p β) (i : ι)
variable (p) in
end
section Single
variable [DecidableEq ι]
variable {β}
section Zero
variable [∀ i, Zero (β i)]
end Zero
section AddCommGroup
variable [∀ i, AddCommGroup (β i)]
end AddCommGroup
section LinearIndependent
end LinearIndependent
end Single
section DistNorm
variable [Fintype ι]
section EDist
variable [∀ i, EDist (β i)]
variable {β}
end EDist
section EDistProp
variable {β}
variable [∀ i, PseudoEMetricSpace (β i)]
end EDistProp
section Dist
variable [∀ i, Dist (α i)]
variable {α}
end Dist
section Norm
variable [∀ i, Norm (β i)]
variable {p β}
end Norm
end DistNorm
section Aux
variable [Fact (1 ≤ p)] [∀ i, PseudoMetricSpace (α i)] [∀ i, PseudoEMetricSpace (β i)]
variable [Fintype ι]
attribute [local instance] PiLp.pseudoEmetricAux
set_option backward.isDefEq.respectTransparency false in
attribute [local instance] PiLp.pseudoMetricAux
variable {p β} in
set_option backward.privateInPublic true in
set_option backward.privateInPublic true in
end Aux
section Fintype
variable [hp : Fact (1 ≤ p)]
variable [Fintype ι]
set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
section
variable {β p}
end
section
variable {β p}
end
section Linfty
variable {β}
variable [∀ i, SeminormedAddCommGroup (β i)]
end Linfty
section L1
variable {β} [∀ i, SeminormedAddCommGroup (β i)]
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency false in
end L1
section L2
variable {β} [∀ i, SeminormedAddCommGroup (β i)]
end L2
variable {𝕜 p α}
variable [Semiring 𝕜] [∀ i, SeminormedAddCommGroup (α i)] [∀ i, SeminormedAddCommGroup (β i)]
variable [∀ i, Module 𝕜 (α i)] [∀ i, Module 𝕜 (β i)]
section piLpCongrLeft
variable {ι' : Type*}
variable [Fintype ι']
variable (p 𝕜)
variable (E : Type*) [SeminormedAddCommGroup E] [Module 𝕜 E]
variable {p 𝕜 E}
end piLpCongrLeft
section piLpCongrRight
variable {β}
variable (p) in
end piLpCongrRight
section piLpExtendByZero
variable {ι' : Type*} [Fintype ι'] {E : Type*} [SeminormedAddCommGroup E] [Module 𝕜 E]
variable (p 𝕜 E) in

@[simp]
theorem _root_.LinearIsometry.piLpExtendByZero_apply_single [DecidableEq ι] [DecidableEq ι']
    (f : ι ↪ ι') (i : ι) (a : E) :
    LinearIsometry.piLpExtendByZero p 𝕜 E f (PiLp.single p i a) = PiLp.single p (f i) a := by
  ext j
  simp only [LinearIsometry.piLpExtendByZero] at *
  simp only [PiLp.single_apply] at *
  by_cases h : ∃ k, f k = j
  · obtain ⟨k, rfl⟩ := h
    simp [f.injective.extend_apply, Pi.single_apply, f.injective.eq_iff]
  · push_neg at h
    simp [Function.extend_apply' _ _ _ (by push_neg; exact h), Pi.single_apply,
      Ne.symm (h i)]
