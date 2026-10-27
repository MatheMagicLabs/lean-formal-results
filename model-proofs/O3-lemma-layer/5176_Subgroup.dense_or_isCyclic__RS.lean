/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     Subgroup.dense_or_isCyclic
Source:      Mathlib @ a02a63c2, Mathlib/Topology/Algebra/Order/ArchimedeanDiscrete.lean, line 61
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  O3-lemma-layer, arm RS, verified in round 0 (round 0 = first attempt)
Prover:      claude-opus-5-5
Setup:       Opus 5.5 with repair loop: arm R = repair only; arm RS = repair plus the Lean-checked lemma layer
Check:       the proof replaced the human proof in the Mathlib file above; Lean reported
             0 errors and no `sorry`; sorry/admit/native_decide/search tactics were rejected.
-/

namespace Subgroup
variable {G : Type*} [CommGroup G] [LinearOrder G] [IsOrderedMonoid G]
variable [MulArchimedean G]

@[to_additive dense_or_isCyclic
/-- An additive subgroup of an archimedean linear ordered additive commutative group `G`
with order topology either is dense in `G` or is a cyclic subgroup. -/]
theorem dense_or_isCyclic (H : Subgroup G) : Dense (H : Set G) ∨ IsCyclic H := by
  refine (em _).imp (dense_of_not_isolated_one H) fun h => ?_
  push_neg at h
  rcases h with ⟨ε, ε1, hε⟩
  exact isCyclic_of_disjoint_Ioo_one ε1 (Set.disjoint_left.2 fun g hg => hε g hg)
