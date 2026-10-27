/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     IsQuotientCoveringMap.fundamentalGroupToMulOpposite_eq
Source:      Mathlib @ a02a63c2, Mathlib/Topology/Homotopy/Lifting.lean, line 683
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  O3LA-leanstral-agent, arm -, verified in final
Prover:      labs-leanstral-1-5
Setup:       Leanstral 1.5 as a tool-using agent (Mistral Vibe)
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

theorem fundamentalGroupToMulOpposite_eq [IsMulCommutative G] (e' : p ⁻¹' {x}) :
    hp.fundamentalGroupToMulOpposite e = hp.fundamentalGroupToMulOpposite e' := by
  ext γ
  apply_fun MulOpposite.unop using MulOpposite.unop_injective
  let g0 := hp.fiberEquivGroup e e'
  have h_eq_fiber : hp.toPermFiber x g0 e = e' :=
    Subtype.ext (hp.fiberEquivGroup_smul_self e)
  have h_smul_e : g0 • (e : E) = (e' : E) := hp.fiberEquivGroup_smul_self e
  have h_mono_val : (hp.isCoveringMap.monodromy γ.asHom e' : E) = g0 • (hp.isCoveringMap.monodromy γ.asHom e : E) := by
    rw [← h_eq_fiber, hp.monodromy_toPermFiber]; rfl
  set a' := (hp.fundamentalGroupToMulOpposite e' γ).unop with ha'
  set a := (hp.fundamentalGroupToMulOpposite e γ).unop with ha
  have ha_smul : a • (e : E) = (hp.isCoveringMap.monodromy γ.asHom e : E) := by
    rw [ha, hp.unop_fundamentalGroupToMulOpposite_smul]
  have ha'_smul : a' • (e' : E) = (hp.isCoveringMap.monodromy γ.asHom e' : E) := by
    rw [ha', hp.unop_fundamentalGroupToMulOpposite_smul]
  have h_comm : g0 • (a' • (e : E)) = g0 • (a • (e : E)) := by
    calc
      g0 • (a' • (e : E)) = (g0 * a') • (e : E) := by rw [← mul_smul]
      _ = (a' * g0) • (e : E) := by rw [mul_comm' g0 a']
      _ = a' • (g0 • (e : E)) := by rw [mul_smul]
      _ = a' • (e' : E) := by rw [h_smul_e]
      _ = (hp.isCoveringMap.monodromy γ.asHom e' : E) := by rw [ha'_smul]
      _ = g0 • (hp.isCoveringMap.monodromy γ.asHom e : E) := by rw [h_mono_val]
      _ = g0 • (a • (e : E)) := by rw [ha_smul]
  have h_eq_smul : a' • (e : E) = a • (e : E) :=
    hp.isCancelSMul.left_cancel' g0 (a' • (e : E)) (a • (e : E)) h_comm
  exact (hp.isCancelSMul.right_cancel' a' a (e : E) h_eq_smul).symm
