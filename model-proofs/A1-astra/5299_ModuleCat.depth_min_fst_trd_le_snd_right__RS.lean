/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     ModuleCat.depth_min_fst_trd_le_snd_right
Source:      Mathlib @ a02a63c2, Mathlib/RingTheory/Depth/Basic.lean, line 264
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  A1-astra, arm RS, verified in round 3 (round 0 = first attempt)
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

@[stacks 00LX "(1)"]
lemma depth_min_fst_trd_le_snd_right
    (N : ModuleCat.{v} R) (S : ShortComplex (ModuleCat.{v} R)) (hS : S.ShortExact) :
    N.depth S.X₁ ⊓ N.depth S.X₃ ≤ N.depth S.X₂ := by
  have vanishing (M : ModuleCat.{v} R) (n : ℕ)
      (hn : (n : ℕ∞) < N.depth M) : Subsingleton (Ext N M n) := by
    generalize hd : N.depth M = d at hn
    induction d using ENat.recTopCoe with
    | top =>
        exact (ModuleCat.depth_eq_top_iff N M).mp hd n
    | coe k =>
        exact ((ModuleCat.depth_eq_iff N M k).mp hd).2 n
          (by exact_mod_cast hn)
  by_contra h
  have hlt := lt_of_not_ge h
  generalize hd : N.depth S.X₂ = d at hlt
  induction d using ENat.recTopCoe with
  | top => simp at hlt
  | coe n =>
      haveI := vanishing S.X₁ n (lt_of_lt_of_le hlt inf_le_left)
      haveI := vanishing S.X₃ n (lt_of_lt_of_le hlt inf_le_right)
      haveI := ((ModuleCat.depth_eq_iff N S.X₂ n).mp hd).1
      have hz : ∀ e : Ext N S.X₂ n, e = 0 := by
        intro e
        obtain ⟨e', rfl⟩ :=
          Ext.covariant_sequence_exact₂ N hS e (Subsingleton.elim _ _)
        simp [show e' = 0 from Subsingleton.elim _ _]
      obtain ⟨a, b, hab⟩ := exists_pair_ne (Ext N S.X₂ n)
      exact hab ((hz a).trans (hz b).symm)
