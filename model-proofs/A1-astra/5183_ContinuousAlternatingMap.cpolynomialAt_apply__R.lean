/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     ContinuousAlternatingMap.cpolynomialAt_apply
Source:      Mathlib @ a02a63c2, Mathlib/Analysis/Analytic/CPolynomial.lean, line 459
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  A1-astra, arm R, verified in round 2 (round 0 = first attempt)
Prover:      gpt-6-astra
Setup:       GPT-6 Astra (Codex, effort medium): R = proof plus up to 3 repair rounds with Lean errors; RS = R plus lemma layer; RT = R with read-only Mathlib sources to search; N0-N3 = independent attempts
Check:       the proof replaced the human proof in the Mathlib file above; Lean reported
             0 errors and no `sorry`; sorry/admit/native_decide/search tactics were rejected.
-/

variable {𝕜 E F G : Type*} [NontriviallyNormedField 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
open scoped Topology Nat
open Set Filter ENNReal
variable {f g : E → F} {p pf pg : FormalMultilinearSeries 𝕜 E F} {x : E} {r : ℝ≥0∞} {n m : ℕ}
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency false in
namespace ContinuousMultilinearMap
variable {ι : Type*} {Em : ι → Type*} [∀ i, NormedAddCommGroup (Em i)] [∀ i, NormedSpace 𝕜 (Em i)]
end ContinuousMultilinearMap
namespace ContinuousAlternatingMap
variable {ι : Type*} [Fintype ι] (f : E [⋀^ι]→L[𝕜] F) {x : Π (_ : ι), E} {s : Set (Π (_ : ι), E)}
variable [CharZero 𝕜]
end ContinuousAlternatingMap
namespace ContinuousLinearMap
variable {ι : Type*} {Em : ι → Type*} [∀ i, NormedAddCommGroup (Em i)] [∀ i, NormedSpace 𝕜 (Em i)]
end ContinuousLinearMap
namespace ContinuousMultilinearMap
variable {ι : Type*} {Em Fm : ι → Type*}
variable {t : Set ((Π i, Fm i →L[𝕜] Em i) × (ContinuousMultilinearMap 𝕜 Em G))}
end ContinuousMultilinearMap
namespace ContinuousAlternatingMap
variable {ι : Type*} [Fintype ι] {f : (E [⋀^ι]→L[𝕜] F) × (ι → E)}

lemma cpolynomialAt_apply :
    CPolynomialAt 𝕜 (fun (p : (E [⋀^ι]→L[𝕜] F) × (ι → E)) ↦ p.1 p.2) f := by
  exact ContinuousMultilinearMap.cpolynomialAt_apply.comp <|
    ((((toContinuousMultilinearMapCLM 𝕜).comp
      (ContinuousLinearMap.fst 𝕜 _ _)).prod
      (ContinuousLinearMap.snd 𝕜 _ _)).cpolynomialAt f)
