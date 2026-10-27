/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     baireSpace_iff_interior_iUnion_eq_empty
Source:      Mathlib @ a02a63c2, Mathlib/Topology/Baire/Lemmas.lean, line 49
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  O3LA-leanstral-agent, arm -, verified in final
Prover:      labs-leanstral-1-5
Setup:       Leanstral 1.5 as a tool-using agent (Mistral Vibe)
Check:       the proof replaced the human proof in the Mathlib file above; Lean reported
             0 errors and no `sorry`; sorry/admit/native_decide/search tactics were rejected.
-/

open scoped Topology
open Filter Set TopologicalSpace
variable {X α : Type*} {ι : Sort*}
section BaireTheorem
variable [TopologicalSpace X]

theorem baireSpace_iff_interior_iUnion_eq_empty :
    BaireSpace X ↔ ∀ f : ℕ → Set X,
      (∀ n, IsClosed (f n)) → (∀ n, IsNowhereDense (f n)) → interior (⋃ n, f n) = ∅ := by
  constructor
  · intro hB f hf_closed hf_nowhere
    have h_open : ∀ n, IsOpen ((f n)ᶜ) := fun n ↦
      isOpen_compl_iff.mpr (hf_closed n)
    have h_dense : ∀ n, Dense ((f n)ᶜ) := fun n ↦
      (isClosed_isNowhereDense_iff_compl.1 ⟨hf_closed n, hf_nowhere n⟩).2
    have h_dense_inter : Dense (⋂ n, (f n)ᶜ) :=
      hB.baire_property (fun n ↦ (f n)ᶜ) h_open h_dense
    have h_eq : (⋂ n, (f n)ᶜ) = (⋃ n, f n)ᶜ := by
      simp [compl_iUnion]
    rw [h_eq] at h_dense_inter
    exact interior_eq_empty_iff_dense_compl.mpr h_dense_inter
  · intro h
    refine ⟨fun f hf_open hf_dense ↦ ?_⟩
    rw [dense_iff_inter_open]
    intro U hU_open hU_ne
    by_contra! h_empty
    have h_subset : U ⊆ ⋃ n, (f n)ᶜ := by
      intro x hxU
      have hx_notin_inter : x ∉ ⋂ n, f n := by
        intro hx_inter
        have hx_mem : x ∈ U ∩ (⋂ n, f n) := ⟨hxU, hx_inter⟩
        rw [h_empty] at hx_mem
        simp at hx_mem
      rw [mem_iInter, not_forall] at hx_notin_inter
      rcases hx_notin_inter with ⟨n, hx_notin_fn⟩
      exact mem_iUnion.mpr ⟨n, hx_notin_fn⟩
    have h_closed_nowhere : ∀ n, IsClosed ((f n)ᶜ) ∧ IsNowhereDense ((f n)ᶜ) := by
      intro n
      have h_closed : IsClosed ((f n)ᶜ) :=
        isClosed_compl_iff.mpr (hf_open n)
      have h_nowhere : IsNowhereDense ((f n)ᶜ) := by
        rw [IsClosed.isNowhereDense_iff h_closed]
        exact (hf_dense n).interior_compl
      exact ⟨h_closed, h_nowhere⟩
    have h_interior_empty : interior (⋃ n, (f n)ᶜ) = ∅ :=
      h (fun n ↦ (f n)ᶜ) (fun n ↦ (h_closed_nowhere n).1) (fun n ↦ (h_closed_nowhere n).2)
    have hU_subset_interior : U ⊆ interior (⋃ n, (f n)ᶜ) := by
      calc
        U = interior U := (hU_open.interior_eq).symm
        _ ⊆ interior (⋃ n, (f n)ᶜ) := interior_mono h_subset
    rw [h_interior_empty] at hU_subset_interior
    have hU_empty : U = ∅ := by
      rw [Set.eq_empty_iff_forall_notMem]
      intro x hxU
      exact hU_subset_interior hxU
    rw [hU_empty] at hU_ne
    rcases hU_ne with ⟨x, hx⟩
    simp at hx
