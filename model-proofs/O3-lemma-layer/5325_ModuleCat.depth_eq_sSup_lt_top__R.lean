/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     ModuleCat.depth_eq_sSup_lt_top
Source:      Mathlib @ a02a63c2, Mathlib/RingTheory/Depth/Basic.lean, line 144
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  O3-lemma-layer, arm R, verified in round 0 (round 0 = first attempt)
Prover:      claude-opus-5-5
Setup:       Opus 5.5 with repair loop: arm R = repair only; arm RS = repair plus the Lean-checked lemma layer
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
    rcases eq_or_ne n ⊤ with rfl | hne
    · by_contra hlt
      push_neg at hlt
      obtain ⟨k, hk⟩ := ENat.ne_top_iff_exists.mp hlt.ne
      have hmem : ((k + 1 : ℕ) : ℕ∞) ∈
          {n : ℕ∞ | n < ⊤ ∧ ∀ i : ℕ, i < n → Subsingleton (Ext N M i)} :=
        ⟨ENat.coe_lt_top _, fun i _ => hn i (ENat.coe_lt_top i)⟩
      have h1 := le_sSup hmem
      rw [← hk] at h1
      have h2 := ENat.coe_le_coe.mp h1
      omega
    · exact le_sSup ⟨lt_top_iff_ne_top.mpr hne, hn⟩
  · exact sSup_le_sSup (fun n hn => hn.2)
