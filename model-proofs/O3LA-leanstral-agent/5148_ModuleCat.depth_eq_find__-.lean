/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     ModuleCat.depth_eq_find
Source:      Mathlib @ a02a63c2, Mathlib/RingTheory/Depth/Basic.lean, line 84
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

private lemma depth_eq_find (N M : ModuleCat.{v} R) (h : ∃ n, Nontrivial (Ext N M n)) :
    N.depth M = Nat.find h := by
  set k := Nat.find h with hk_def
  have hk_spec : Nontrivial (Ext N M k) := Nat.find_spec h
  have hk_min : ∀ m, m < k → ¬ Nontrivial (Ext N M m) := by
    intro m hm
    apply Nat.find_min h
    rwa [← hk_def]
  have h0 : (0 : ℕ∞) ∈ {n : ℕ∞ | ∀ i : ℕ, i < n → Subsingleton (Ext N M i)} := by
    refine Set.mem_setOf.mpr fun i hi => ?_
    have : ¬ ((i : ℕ∞) < (0 : ℕ∞)) := by
      simpa [WithTop.coe_lt_coe] using Nat.not_lt_zero i
    exact absurd hi this
  have hk_mem : (k : ℕ∞) ∈ {n : ℕ∞ | ∀ i : ℕ, i < n → Subsingleton (Ext N M i)} := by
    refine Set.mem_setOf.mpr fun i hi => ?_
    have hi_lt_k : i < k := by
      simpa [WithTop.coe_lt_coe] using hi
    have h_not_nontrivial : ¬ Nontrivial (Ext N M i) := hk_min i hi_lt_k
    exact (not_nontrivial_iff_subsingleton.mp h_not_nontrivial)
  have h_upper_bound : ∀ a ∈ {n : ℕ∞ | ∀ i : ℕ, i < n → Subsingleton (Ext N M i)}, a ≤ (k : ℕ∞) := by
    intro a ha
    by_contra! h_lt
    have ha_mem : ∀ i : ℕ, i < a → Subsingleton (Ext N M i) := Set.mem_setOf.mp ha
    by_cases ha_top : a = ⊤
    · subst ha_top
      have h_subsingleton : Subsingleton (Ext N M k) := ha_mem k (ENat.natCast_lt_top k)
      haveI := h_subsingleton
      exact (not_nontrivial (Ext N M k)) hk_spec
    · obtain ⟨m, rfl⟩ := WithTop.ne_top_iff_exists.mp ha_top
      have hk_lt_m : (k : ℕ∞) < (m : ℕ∞) := h_lt
      have h_subsingleton : Subsingleton (Ext N M k) := ha_mem k hk_lt_m
      haveI := h_subsingleton
      exact (not_nontrivial (Ext N M k)) hk_spec
  have h_least_upper_bound : ∀ ub, (∀ a ∈ {n : ℕ∞ | ∀ i : ℕ, i < n → Subsingleton (Ext N M i)}, a ≤ ub) → (k : ℕ∞) ≤ ub := by
    intro ub hub
    exact hub (k : ℕ∞) hk_mem
  dsimp [ModuleCat.depth]
  exact csSup_eq_of_is_forall_le_of_forall_le_imp_ge ⟨0, h0⟩ h_upper_bound h_least_upper_bound
