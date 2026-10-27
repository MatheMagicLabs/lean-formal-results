/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     ModuleCat.depth_eq_iff
Source:      Mathlib @ a02a63c2, Mathlib/RingTheory/Depth/Basic.lean, line 124
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  O3-lemma-layer, arm R, verified in round 1 (round 0 = first attempt)
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

lemma depth_eq_iff (N M : ModuleCat.{v} R) (n : ℕ) : N.depth M = n ↔
    Nontrivial (Ext N M n) ∧ ∀ i < n, Subsingleton (Ext N M i) := by
  have key : ∀ m : ℕ∞, (m ≤ N.depth M ↔
      ∀ i : ℕ, (i : ℕ∞) < m → Subsingleton (Ext N M i)) := by
    intro m
    unfold ModuleCat.depth
    constructor
    · intro hm i hi
      obtain ⟨k, hk, hik⟩ := lt_sSup_iff.mp (lt_of_lt_of_le hi hm)
      exact hk i hik
    · intro h
      exact le_sSup h
  constructor
  · intro h
    have h1 := (key n).1 h.ge
    refine ⟨?_, fun i hi => h1 i (by exact_mod_cast hi)⟩
    rw [← not_subsingleton_iff_nontrivial]
    intro hs
    have hall : ∀ i : ℕ, (i : ℕ∞) < ((n + 1 : ℕ) : ℕ∞) → Subsingleton (Ext N M i) := by
      intro i hi
      have hi' : i < n + 1 := by exact_mod_cast hi
      rcases Nat.lt_succ_iff_lt_or_eq.mp hi' with hlt | heq
      · exact h1 i (by exact_mod_cast hlt)
      · subst heq
        exact hs
    have := (key _).2 hall
    rw [h] at this
    have h2 : n + 1 ≤ n := by exact_mod_cast this
    omega
  · rintro ⟨ntr, h⟩
    apply le_antisymm
    · by_contra hc
      push_neg at hc
      have hle : (n : ℕ∞) + 1 ≤ N.depth M := by
        first
          | exact (ENat.add_one_le_iff (ENat.coe_ne_top n)).2 hc
          | exact Order.add_one_le_of_lt hc
      have hlt : (n : ℕ∞) < (n : ℕ∞) + 1 := by
        first
          | exact_mod_cast Nat.lt_succ_self n
          | exact ENat.lt_add_one_iff (ENat.coe_ne_top n) |>.2 le_rfl
          | exact Order.lt_add_one_iff.2 le_rfl
      have := (key ((n : ℕ∞) + 1)).1 hle n hlt
      exact (not_subsingleton_iff_nontrivial.mpr ntr) this
    · exact (key n).2 (fun i hi => h i (by exact_mod_cast hi))
