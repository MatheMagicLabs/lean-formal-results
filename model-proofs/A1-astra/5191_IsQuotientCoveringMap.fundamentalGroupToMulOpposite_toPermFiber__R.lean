/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     IsQuotientCoveringMap.fundamentalGroupToMulOpposite_toPermFiber
Source:      Mathlib @ a02a63c2, Mathlib/Topology/Homotopy/Lifting.lean, line 674
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  A1-astra, arm R, verified in round 3 (round 0 = first attempt)
Prover:      gpt-6-astra
Setup:       GPT-6 Astra (Codex, effort medium): R = proof plus up to 3 repair rounds with Lean errors; RS = R plus lemma layer; RT = R with read-only Mathlib sources to search; N0-N3 = independent attempts
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
  classical
  have h (a : p ⁻¹' {x}) :
      hp.toPermFiber x (hp.fiberEquivGroup e a) e = a :=
    (hp.fiberEquivGroup e).symm_apply_apply a
  apply MulOpposite.unop_injective
  change hp.fiberEquivGroup (hp.toPermFiber x g e) _ =
    g * hp.fiberEquivGroup e _ * g⁻¹
  apply (hp.fiberEquivGroup (hp.toPermFiber x g e)).symm.injective
  rw [Equiv.symm_apply_apply]
  change _ = hp.toPermFiber x (g * hp.fiberEquivGroup e _ * g⁻¹)
    (hp.toPermFiber x g e)
  rw [hp.monodromy_toPermFiber]
  simp [map_mul, Equiv.Perm.mul_apply, h]
