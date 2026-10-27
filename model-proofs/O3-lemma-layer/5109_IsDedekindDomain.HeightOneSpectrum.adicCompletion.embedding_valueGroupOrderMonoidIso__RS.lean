/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     IsDedekindDomain.HeightOneSpectrum.adicCompletion.embedding_valueGroupOrderMonoidIso
Source:      Mathlib @ a02a63c2, Mathlib/RingTheory/DedekindDomain/AdicValuation.lean, line 721
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  O3-lemma-layer, arm RS, verified in round 1 (round 0 = first attempt)
Prover:      claude-opus-5-5
Setup:       Opus 5.5 with repair loop: arm R = repair only; arm RS = repair plus the Lean-checked lemma layer
Check:       the proof replaced the human proof in the Mathlib file above; Lean reported
             0 errors and no `sorry`; sorry/admit/native_decide/search tactics were rejected.
-/

noncomputable section
open WithZero Multiplicative IsDedekindDomain
variable {R : Type*} [CommRing R] [IsDedekindDomain R] {K S : Type*} [Field K] [CommSemiring S]
namespace IsDedekindDomain.HeightOneSpectrum
open scoped Classical in
open scoped Classical in
variable (K) in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency.types false in
open scoped algebraMap in
open scoped algebraMap in
open scoped algebraMap in
open scoped algebraMap in
variable (K) in
open scoped algebraMap in
variable (K)
open scoped algebraMap in
variable {K} in
variable {K}
section Localization
open Localization
local instance : IsDedekindDomain
local instance : IsLocalRing (subalgebra.ofField K _ v.asIdeal.primeCompl_le_nonZeroDivisors) :=
variable (K) in
open IsDedekindDomain
open scoped algebraMap in
end Localization
variable (K)
section Notation
open Lean.PrettyPrinter.Delaborator
end Notation
namespace adicCompletion
open UniformSpace MonoidWithZeroHom MonoidWithZeroHom.ValueGroup₀ Filter Topology Valuation

theorem embedding_valueGroupOrderMonoidIso (g : (valuation K v).ValueGroup₀) :
    embedding (valueGroupOrderMonoidIso K v g) = embedding g := by
  induction g using WithZero.recZeroCoe with
  | zero =>
    first
    | simp
    | rw [map_zero]
  | coe a =>
    rw [valueGroupOrderMonoidIso_coe]
    have h := coe_valueGroupMulEquiv K v a
    first
    | exact congrArg (fun u : ℤᵐ⁰ˣ => (u : ℤᵐ⁰)) h
    | (simp only [embedding] at *; exact congrArg (fun u : ℤᵐ⁰ˣ => (u : ℤᵐ⁰)) h)
    | (simp [embedding]; exact congrArg (fun u : ℤᵐ⁰ˣ => (u : ℤᵐ⁰)) h)
    | (simp [embedding, h])
    | (unfold embedding; simp [h])
