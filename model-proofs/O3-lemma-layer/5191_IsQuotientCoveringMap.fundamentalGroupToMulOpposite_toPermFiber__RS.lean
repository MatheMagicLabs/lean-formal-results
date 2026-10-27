/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     IsQuotientCoveringMap.fundamentalGroupToMulOpposite_toPermFiber
Source:      Mathlib @ a02a63c2, Mathlib/Topology/Homotopy/Lifting.lean, line 674
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  O3-lemma-layer, arm RS, verified in round 1 (round 0 = first attempt)
Prover:      claude-opus-5-5
Setup:       Opus 5.5 with repair loop: arm R = repair only; arm RS = repair plus the Lean-checked lemma layer
Check:       the proof replaced the human proof in the Mathlib file above; Lean reported
             0 errors and no `sorry`; sorry/admit/native_decide/search tactics were rejected.
-/

noncomputable section
open Function Topology unitInterval
variable {E X A : Type*} [TopologicalSpace E] [TopologicalSpace X] [TopologicalSpace A] {p : E → X}
namespace IsLocalHomeomorph
variable (homeo : IsLocalHomeomorph p)
variable (sep : IsSeparatedMap p)
open PathConnectedSpace (somePath) in
end IsLocalHomeomorph
namespace IsCoveringMap
variable (cov : IsCoveringMap p)
section path_lifting
variable (γ : C(I, X)) (e : E) (γ_0 : γ 0 = p e)
variable {γ e}
end path_lifting
section homotopy_lifting
variable (H : C(I × A, X)) (f : C(A, E)) (H_0 : ∀ a, H (0, a) = p (f a))
variable {H f}
variable {f₀ f₁ : C(A, X)} {S : Set A} (F : f₀.HomotopyRel f₁ S)
set_option backward.isDefEq.respectTransparency.types false in
open ContinuousMap in
set_option backward.isDefEq.respectTransparency.types false in
open CategoryTheory
open FundamentalGroup Path.Homotopic.Quotient in
end homotopy_lifting
end IsCoveringMap
namespace IsQuotientCoveringMap
variable {G : Type*} [Group G] [MulAction G E] (hp : IsQuotientCoveringMap p G) {g : G}
set_option backward.isDefEq.respectTransparency.types false in
variable {x : X} (e : p ⁻¹' {x}) {γ : FundamentalGroup X x}
set_option backward.isDefEq.respectTransparency.types false in
open MulOpposite in
variable {e} in
variable {e} in
variable {e} in
variable {e} in

theorem fundamentalGroupToMulOpposite_toPermFiber :
    hp.fundamentalGroupToMulOpposite (hp.toPermFiber x g e) γ =
      MulOpposite.op (g * (hp.fundamentalGroupToMulOpposite e γ).unop * g⁻¹) := by
  rw [fundamentalGroupToMulOpposite_apply_eq_iff]
  have h2 := congrArg (fun ψ => ((ψ e : p ⁻¹' {x}) : E))
    (hp.commute_monodromyPerm_toPermFiber (g := g) (γ := γ)).eq
  simp only [Equiv.Perm.mul_apply] at h2
  change _ = ((hp.isCoveringMap.monodromyPerm x γ (hp.toPermFiber x g e) : p ⁻¹' {x}) : E)
  rw [h2]
  have h3 : ((hp.toPermFiber x g e : p ⁻¹' {x}) : E) = g • e.1 := rfl
  have h4 : ((hp.toPermFiber x g (hp.isCoveringMap.monodromyPerm x γ e) : p ⁻¹' {x}) : E)
      = g • ((hp.isCoveringMap.monodromyPerm x γ e : p ⁻¹' {x}) : E) := rfl
  rw [h3, h4, MulOpposite.unop_op, mul_smul, mul_smul, inv_smul_smul]
  congr 1
  rw [unop_fundamentalGroupToMulOpposite_smul]
  rfl
