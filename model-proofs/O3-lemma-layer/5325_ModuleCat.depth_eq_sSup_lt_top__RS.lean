/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     ModuleCat.depth_eq_sSup_lt_top
Source:      Mathlib @ a02a63c2, Mathlib/RingTheory/Depth/Basic.lean, line 144
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  O3-lemma-layer, arm RS, verified in round 0 (round 0 = first attempt)
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
  apply le_antisymm
  · by_cases hd : N.depth M = ⊤
    · rw [hd]
      have hS : ∀ k : ℕ, (k : ℕ∞) ∈
          {n : ℕ∞ | n < ⊤ ∧ ∀ i : ℕ, i < n → Subsingleton (Ext N M i)} :=
        fun k => ⟨ENat.natCast_lt_top k, fun i _ => (depth_eq_top_iff N M).mp hd i⟩
      by_contra hs
      obtain ⟨k, hk⟩ := ENat.ne_top_iff_exists.mp (fun h => hs h.ge)
      have h1 := le_sSup (hS (k + 1))
      rw [← hk] at h1
      norm_cast at h1
      omega
    · obtain ⟨k, hk⟩ := ENat.ne_top_iff_exists.mp hd
      rw [← hk]
      apply le_sSup
      refine ⟨ENat.natCast_lt_top k, fun i hi => subsingleton_ext_of_lt_depth ?_⟩
      rw [← hk]
      exact hi
  · apply sSup_le
    rintro m ⟨hm, hsub⟩
    by_contra hlt
    push_neg at hlt
    have hd : N.depth M ≠ ⊤ := ne_top_of_lt (lt_trans hlt hm)
    obtain ⟨k, hk⟩ := ENat.ne_top_iff_exists.mp hd
    have h1 := ((depth_eq_iff N M k).mp hk.symm).1
    have h2 := hsub k (by rw [hk]; exact hlt)
    obtain ⟨x, y, hxy⟩ := h1.exists_pair_ne
    exact hxy (@Subsingleton.elim _ h2 x y)
