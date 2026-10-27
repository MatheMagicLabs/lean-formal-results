/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     IsQuotientCoveringMap.fundamentalGroupToMulOpposite_eq
Source:      Mathlib @ a02a63c2, Mathlib/Topology/Homotopy/Lifting.lean, line 683
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  O3-lemma-layer, arm RS, verified in round 0 (round 0 = first attempt)
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

theorem fundamentalGroupToMulOpposite_eq [IsMulCommutative G] (e' : p ⁻¹' {x}) :
    hp.fundamentalGroupToMulOpposite e = hp.fundamentalGroupToMulOpposite e' := by
  obtain ⟨g, rfl⟩ := hp.exists_toPermFiber_eq e e'
  have hc : ∀ a b : G, a * b = b * a := fun a b => IsMulCommutative.is_comm.comm a b
  refine MonoidHom.ext fun γ => ?_
  rw [fundamentalGroupToMulOpposite_toPermFiber, hc g]
  simp
