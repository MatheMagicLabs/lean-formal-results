/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     IsDedekindDomain.HeightOneSpectrum.adicCompletion.embedding_valueGroupOrderMonoidIso
Source:      Mathlib @ a02a63c2, Mathlib/RingTheory/DedekindDomain/AdicValuation.lean, line 721
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  O3LA2-leanstral-agent-variants, arm staffel, verified in final
Prover:      labs-leanstral-1-5
Setup:       Leanstral 1.5 agent on the 29 theorems O3LA left open: neu = fresh restart, fest = fixed instruction, staffel = staged budget
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
  match g with
  | 0 => simp
  | .coe g =>
    dsimp [valueGroupOrderMonoidIso, valueGroupMulEquiv]
    rfl
