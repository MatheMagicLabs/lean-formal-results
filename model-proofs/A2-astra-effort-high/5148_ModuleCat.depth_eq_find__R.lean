/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     ModuleCat.depth_eq_find
Source:      Mathlib @ a02a63c2, Mathlib/RingTheory/Depth/Basic.lean, line 84
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  A2-astra-effort-high, arm R, verified in round 1 (round 0 = first attempt)
Prover:      gpt-6-astra
Setup:       GPT-6 Astra, reasoning effort high (arms R, N0)
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
  classical
  unfold depth
  apply le_antisymm
  · refine sSup_le fun n hn => ?_
    by_contra hle
    haveI : Subsingleton (Ext N M (Nat.find h)) :=
      hn (Nat.find h) (lt_of_not_ge hle)
    obtain ⟨a, b, hab⟩ := (Nat.find_spec h).exists_pair_ne
    exact hab (Subsingleton.elim a b)
  · refine le_sSup ?_
    intro i hi
    rcases subsingleton_or_nontrivial (Ext N M i) with hs | hn
    · exact hs
    · have hmin : Nat.find h ≤ i := Nat.find_min' h hn
      have hlt : i < Nat.find h := by exact_mod_cast hi
      exact (Nat.not_lt_of_ge hmin hlt).elim
