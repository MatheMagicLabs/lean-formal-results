/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     IsCoveringMap.monodromy_eq_apply_one
Source:      Mathlib @ a02a63c2, Mathlib/Topology/Homotopy/Lifting.lean, line 396
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  A1-astra, arm RS, verified in round 1 (round 0 = first attempt)
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

lemma monodromy_eq_apply_one {x y : X} {γ : Path x y} {e : p ⁻¹' {x}} {Γ : C(I, E)}
    (hpΓ : p ∘ Γ = γ) (Γ_0 : Γ 0 = e) : cov.monodromy (.mk γ) e = Γ 1 := by
  rw [cov.coe_monodromy_mk]
  have hΓ : Γ = cov.liftPath γ e (γ.source.trans e.2.symm) :=
    (cov.eq_liftPath_iff' (γ.source.trans e.2.symm)).2 ⟨hpΓ, Γ_0⟩
  exact congrArg (fun δ : C(I, E) => δ 1) hΓ.symm
