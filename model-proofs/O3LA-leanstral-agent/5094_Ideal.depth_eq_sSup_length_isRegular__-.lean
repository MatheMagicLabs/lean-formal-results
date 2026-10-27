/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     Ideal.depth_eq_sSup_length_isRegular
Source:      Mathlib @ a02a63c2, Mathlib/RingTheory/Depth/Basic.lean, line 337
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  O3LA-leanstral-agent, arm -, verified in final
Prover:      labs-leanstral-1-5
Setup:       Leanstral 1.5 as a tool-using agent (Mistral Vibe)
Check:       the proof replaced the human proof in the Mathlib file above; Lean reported
             0 errors and no `sorry`; sorry/admit/native_decide/search tactics were rejected.
-/

open IsLocalRing LinearMap Module
universe v u
open RingTheory.Sequence Ideal CategoryTheory Abelian Limits Pointwise ModuleCat IsSMulRegular
variable {R : Type u} [CommRing R] [Small.{v} R]
section depth
namespace ModuleCat
open Classical in
end ModuleCat

lemma Ideal.depth_eq_sSup_length_isRegular [IsNoetherianRing R] (I : Ideal R)
    (M : ModuleCat.{v} R) [Module.Finite R M] (smul_lt : I • (⊤ : Submodule R M) < ⊤) :
    I.depth M = sSup {(List.length rs : ℕ∞) | (rs : List R)
      (_ : IsRegular M rs) (_ : ∀ r ∈ rs, r ∈ I)} := by
  rw [Ideal.depth]
  haveI : Nontrivial (R ⧸ I) := by
    rw [Ideal.Quotient.nontrivial_iff]
    by_contra h
    have htop : I = ⊤ := by simpa using h
    have hsmul : I • (⊤ : Submodule R M) = ⊤ := by
      simpa [htop] using Ideal.top_smul (⊤ : Submodule R M)
    rw [hsmul] at smul_lt
    exact lt_irrefl _ smul_lt
  exact ModuleCat.depth_eq_sSup_length_isRegular I (↧(Shrink.{v} (R ⧸ I))) M smul_lt
    ((Shrink.linearEquiv R (R ⧸ I)).support_eq.trans (by
      rw [Module.support_eq_zeroLocus, annihilator_quotient]))
