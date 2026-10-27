/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     IsDedekindDomain.HeightOneSpectrum.adicCompletion.embedding_valueGroupOrderMonoidIso
Source:      Mathlib @ a02a63c2, Mathlib/RingTheory/DedekindDomain/AdicValuation.lean, line 721
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  E1-repair-decomposition, arm V, verified in round 1 (round 0 = first attempt)
Prover:      gpt-6-astra
Setup:       GPT-6 Astra, which part of Lean feedback makes repair work: after a shared first attempt (E0), V = full error messages, Z = line numbers only, B = only "Lean rejected this proof"
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
  simp only [valueGroupOrderMonoidIso]
  cases g <;> rfl
