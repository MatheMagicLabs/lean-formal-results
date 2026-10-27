/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     ModuleCat.depth_eq_sSup_lt_top
Source:      Mathlib @ a02a63c2, Mathlib/RingTheory/Depth/Basic.lean, line 144
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  O3LA3-leanstral-agent-feedback, arm rueck, verified in final
Prover:      labs-leanstral-1-5
Setup:       Leanstral 1.5 agent with goal-state feedback (arm rueck)
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
  set S := {n : ℕ∞ | ∀ i : ℕ, i < n → Subsingleton (Ext N M i)}
  set T := {n : ℕ∞ | n < ⊤ ∧ ∀ i : ℕ, i < n → Subsingleton (Ext N M i)}
  have hdepth : N.depth M = sSup S := rfl
  rw [hdepth]
  by_cases htop : N.depth M = ⊤
  · have hall : ∀ i, Subsingleton (Ext N M i) := (depth_eq_top_iff N M).mp htop
    have hsSupS : sSup S = ⊤ := by rw [← hdepth, htop]
    rw [hsSupS]
    symm
    apply (sSup_eq_top (α := ℕ∞)).mpr
    intro b hb
    rcases ENat.exists_nat_gt (ne_top_of_lt hb) with ⟨n, hn⟩
    have hnT : (n : ℕ∞) ∈ T := by
      refine ⟨ENat.natCast_lt_top n, fun i _ => hall i⟩
    exact ⟨(n : ℕ∞), hnT, hn⟩
  · have h_lt_top : N.depth M < ⊤ := lt_top_iff_ne_top.mpr htop
    have hST : S = T := by
      ext n
      constructor
      · intro hn
        have hn_lt_top : n < ⊤ := by
          by_contra! hge
          have hn_top : n = ⊤ := top_unique hge
          subst hn_top
          have htop_mem_S : ⊤ ∈ S := hn
          have htop_le_depth : ⊤ ≤ N.depth M :=
            calc
              ⊤ ≤ sSup S := le_sSup htop_mem_S
              _ = N.depth M := rfl
          exact htop (le_antisymm le_top htop_le_depth)
        exact ⟨hn_lt_top, hn⟩
      · intro ⟨_, hn⟩; exact hn
    rw [hST]
