/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     IsQuotientCoveringMap.fundamentalGroupToMulOpposite_toPermFiber
Source:      Mathlib @ a02a63c2, Mathlib/Topology/Homotopy/Lifting.lean, line 674
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  O3LA2-leanstral-agent-variants, arm staffel, verified in final
Prover:      labs-leanstral-1-5
Setup:       Leanstral 1.5 agent on the 29 theorems O3LA left open: neu = fresh restart, fest = fixed instruction, staffel = staged budget
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
  apply MulOpposite.unop_injective
  dsimp [fundamentalGroupToMulOpposite]
  rw [hp.fiberEquivGroup_eq_iff]
  calc
    (hp.isCoveringMap.monodromy γ.asHom (hp.toPermFiber x g e) : E)
        = (hp.toPermFiber x g (hp.isCoveringMap.monodromy γ.asHom e) : E) := by
      simpa using congrArg Subtype.val (hp.monodromy_toPermFiber (γ := γ.asHom) (e := e) (g := g) (x := x) (y := x))
    _ = g • ((hp.isCoveringMap.monodromy γ.asHom e : p ⁻¹' {x}) : E) := by
      simp
    _ = g • (hp.fiberEquivGroup e (hp.isCoveringMap.monodromy γ.asHom e) • (e : E)) := by
      simp [hp.fiberEquivGroup_smul_self e]
    _ = (g * hp.fiberEquivGroup e (hp.isCoveringMap.monodromy γ.asHom e) * g⁻¹) • (g • (e : E)) := by
      simp [mul_smul]
    _ = (g * hp.fiberEquivGroup e (hp.isCoveringMap.monodromy γ.asHom e) * g⁻¹) •
        ((hp.toPermFiber x g e : p ⁻¹' {x}) : E) := by
      simp
