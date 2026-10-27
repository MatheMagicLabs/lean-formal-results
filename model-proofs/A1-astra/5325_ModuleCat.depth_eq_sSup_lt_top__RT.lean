/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     ModuleCat.depth_eq_sSup_lt_top
Source:      Mathlib @ a02a63c2, Mathlib/RingTheory/Depth/Basic.lean, line 144
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

lemma depth_eq_sSup_lt_top (N M : ModuleCat.{v} R) : N.depth M =
    sSup {n : ℕ∞ | n < ⊤ ∧ ∀ i : ℕ, i < n → Subsingleton (Ext N M i)} := by
  unfold depth
  apply le_antisymm
  · apply sSup_le
    intro n hn
    by_cases h : n = ⊤
    · subst n
      calc
        (⊤ : ℕ∞) = ⨆ k : ℕ, (k : ℕ∞) := ENat.iSup_natCast.symm
        _ ≤ _ := by
          apply iSup_le
          intro k
          apply le_sSup
          exact ⟨by simp, fun i _ => hn i (by simp)⟩
    · exact le_sSup ⟨lt_top_iff_ne_top.mpr h, hn⟩
  · apply sSup_le
    intro n hn
    exact le_sSup hn.2
