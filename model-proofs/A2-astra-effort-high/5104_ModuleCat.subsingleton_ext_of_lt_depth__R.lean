/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     ModuleCat.subsingleton_ext_of_lt_depth
Source:      Mathlib @ a02a63c2, Mathlib/RingTheory/Depth/Basic.lean, line 136
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  A2-astra-effort-high, arm R, verified in round 2 (round 0 = first attempt)
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

lemma subsingleton_ext_of_lt_depth {N M : ModuleCat.{v} R} {i : ℕ}
    (lt : i < N.depth M) : Subsingleton (Ext N M i) := by
  by_contra h
  apply (not_le_of_gt lt)
  unfold ModuleCat.depth
  refine sSup_le fun n hn => ?_
  exact le_of_not_gt fun hi => h (hn i hi)
