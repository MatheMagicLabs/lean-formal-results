/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     Subgroup.dense_or_isCyclic
Source:      Mathlib @ a02a63c2, Mathlib/Topology/Algebra/Order/ArchimedeanDiscrete.lean, line 61
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  A1-astra, arm RS, verified in round 0 (round 0 = first attempt)
Prover:      gpt-6-astra
Setup:       GPT-6 Astra (Codex, effort medium): R = proof plus up to 3 repair rounds with Lean errors; RS = R plus lemma layer; RT = R with read-only Mathlib sources to search; N0-N3 = independent attempts
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
  classical
  by_cases h : ∀ ε : G, 1 < ε → ∃ g ∈ H, g ∈ Set.Ioo 1 ε
  · exact Or.inl (H.dense_of_not_isolated_one h)
  · right
    simp only [not_forall, not_imp] at h
    obtain ⟨a, ha, hgap⟩ := h
    apply Subgroup.isCyclic_of_disjoint_Ioo_one ha
    refine Set.disjoint_left.mpr ?_
    intro g hg hga
    exact hgap ⟨g, hg, hga⟩
