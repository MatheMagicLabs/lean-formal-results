/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     Ideal.depth_eq_sSup_length_isRegular
Source:      Mathlib @ a02a63c2, Mathlib/RingTheory/Depth/Basic.lean, line 337
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  A1-astra, arm RT, verified in round 1 (round 0 = first attempt)
Prover:      gpt-6-astra
Setup:       GPT-6 Astra (Codex, effort medium): R = proof plus up to 3 repair rounds with Lean errors; RS = R plus lemma layer; RT = R with read-only Mathlib sources to search; N0-N3 = independent attempts
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
  rw [Ideal.depth, ModuleCat.depth_eq_sSup_lt_top]
  congr
  ext m
  simp only [exists_prop]
  refine ⟨fun ⟨lt_top, h⟩ ↦ ?_, fun ⟨rs, reg, mem, len⟩ ↦ ?_⟩
  · rcases ENat.ne_top_iff_exists.mp lt_top.ne with ⟨n, hn⟩
    simp only [← hn, Nat.cast_lt, Nat.cast_inj] at h ⊢
    rcases ((ModuleCat.exists_isRegular_tfae I n M smul_lt).out 2 4).mp h with
      ⟨rs, len, mem, reg⟩
    exact ⟨rs, reg, mem, len⟩
  · simp only [← len, ENat.natCast_lt_top, Nat.cast_lt, true_and]
    apply ((ModuleCat.exists_isRegular_tfae I rs.length M smul_lt).out 4 2).mp
    exact ⟨rs, rfl, mem, reg⟩
