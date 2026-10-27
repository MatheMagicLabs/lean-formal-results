/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     ModuleCat.depth_eq_sSup_lt_top
Source:      Mathlib @ a02a63c2, Mathlib/RingTheory/Depth/Basic.lean, line 144
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  O4-layer-with-search, arm RT, verified in round 1 (round 0 = first attempt)
Prover:      claude-opus-5-5
Setup:       Opus 5.5 with repair loop, lemma layer and name search (arm RT)
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
  by_cases h : ∃ n, Nontrivial (Ext N M n)
  · have hlt : N.depth M < ⊤ := (depth_lt_top_iff N M).mpr h
    obtain ⟨n, hn⟩ : ∃ n : ℕ, N.depth M = n :=
      ⟨(N.depth M).toNat, (ENat.coe_toNat hlt.ne).symm⟩
    obtain ⟨hnt, hsub⟩ := (depth_eq_iff N M n).mp hn
    rw [hn]
    apply le_antisymm
    · apply le_sSup
      refine ⟨ENat.coe_lt_top _, fun i hi => ?_⟩
      have : i < n := by exact_mod_cast hi
      exact hsub i this
    · apply sSup_le
      rintro m ⟨hm, hm'⟩
      by_contra hle
      have hlt' := not_le.mp hle
      have := hm' n hlt'
      exact (not_nontrivial_iff_subsingleton.mpr this) hnt
  · have h' : ∀ i, Subsingleton (Ext N M i) := fun i =>
      not_nontrivial_iff_subsingleton.mp (fun hn => h ⟨i, hn⟩)
    rw [(depth_eq_top_iff N M).mpr h']
    symm
    rw [sSup_eq_top]
    intro b hb
    lift b to ℕ using hb.ne
    exact ⟨((b + 1 : ℕ) : ℕ∞), ⟨ENat.coe_lt_top _, fun i _ => h' i⟩,
      by exact_mod_cast Nat.lt_succ_self b⟩
