/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     ModuleCat.subsingleton_ext_of_lt_depth
Source:      Mathlib @ a02a63c2, Mathlib/RingTheory/Depth/Basic.lean, line 136
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  A1-astra, arm RS, verified in round 0 (round 0 = first attempt)
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

lemma subsingleton_ext_of_lt_depth {N M : ModuleCat.{v} R} {i : ℕ}
    (lt : i < N.depth M) : Subsingleton (Ext N M i) := by
  classical
  by_cases h : ∃ n, Nontrivial (Ext N M n)
  · have hd := depth_eq_find N M h
    rw [hd] at lt
    have hi : i < Nat.find h := by exact_mod_cast lt
    exact ((depth_eq_iff N M (Nat.find h)).mp hd).2 i hi
  · rcases subsingleton_or_nontrivial (Ext N M i) with hs | hn
    · exact hs
    · exact (h ⟨i, hn⟩).elim
