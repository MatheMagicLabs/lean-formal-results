/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     ContinuousMap.borel_eq_iSup_comap_eval
Source:      Mathlib @ d0a050ad6, Mathlib/MeasureTheory/Constructions/BorelSpace/ContinuousMap.lean, line 77
             (added after the model's training data; human proof 37 tactic steps)
Experiment:  P1-astra-long-proofs, arm WT, solved after 2 call(s)
Prover:      gpt-6-astra
Setup:       GPT-6 Astra (Codex, effort medium), at most 10 calls per theorem: W = whole proof plus repair rounds;
             WT = W with read-only Mathlib sources to search; P = Lean-checked skeleton of have-steps, then one step per call
Check:       the proof replaced the human proof in the Mathlib file above; Lean reported
             0 errors and no `sorry`.
-/

theorem borel_eq_iSup_comap_eval :
    borel C(X, Y) = ⨆ x : X, (borel Y).comap fun f ↦ f x := by
  classical
  borelize Y
  let m : MeasurableSpace C(X, Y) := ⨆ x : X, (borel Y).comap (fun f ↦ f x)
  have hclosed (K : Set X) (F : Set Y) (hF : IsClosed F) : @MeasurableSet C(X, Y) m {f : C(X, Y) | Set.MapsTo f K F} := by { obtain ⟨D, hDc, hDK, hKD⟩ := TopologicalSpace.exists_countable_dense_subset K; have heq : {f : C(X, Y) | Set.MapsTo f K F} = ⋂ x ∈ D, {f : C(X, Y) | f x ∈ F} := by { ext f; simp only [Set.mem_setOf_eq, Set.mem_iInter]; exact ⟨fun h x hx ↦ h (hDK hx), fun h ↦ (Set.MapsTo.closure_left h f.continuous hF).mono_left hKD⟩ }; rw [heq]; apply MeasurableSet.biInter hDc; intro x hx; exact (le_iSup (fun x : X ↦ (borel Y).comap (fun f : C(X, Y) ↦ f x)) x) _ (MeasurableSpace.measurableSet_comap.mpr ⟨F, hF.measurableSet, rfl⟩) }
  refine le_antisymm ?_ iSup_comap_le_borel
  rw [borel_eq_generateFrom_of_subbasis compactOpen_eq]
  apply MeasurableSpace.generateFrom_le
  rintro _ ⟨K, hK, U, hU, rfl⟩
  let s : Set C(X, Y) := {f | Set.MapsTo f K U}
  have hV : ∀ f : s, ∃ V : Set Y, IsOpen V ∧ (f : C(X, Y)) '' K ⊆ V ∧ closure V ⊆ U := by { intro f; exact (hK.image f.val.continuous).exists_isOpen_closure_subset (hU.mem_nhdsSet.2 f.property.image_subset) }
  choose V hVo hKV hVU using hV
  let W : s → Set C(X, Y) := fun f ↦ {g | Set.MapsTo g K (closure (V f))}
  have hW : ∀ f : s, W f ∈ nhds (f : C(X, Y)) := by { intro f; exact Filter.mem_of_superset (eventually_mapsTo hK (hVo f) (Set.mapsTo_iff_image_subset.mpr (hKV f))) (fun g hg ↦ hg.mono_right subset_closure) }
  obtain ⟨t, htc, htcover⟩ := (HereditarilyLindelofSpace.isLindelof s).elim_nhds_subcover' (fun f hf ↦ W ⟨f, hf⟩) (fun f hf ↦ hW ⟨f, hf⟩)
  have heq : s = ⋃ f ∈ t, W f := by { apply Set.Subset.antisymm htcover; exact Set.iUnion₂_subset fun f _ g hg ↦ hg.mono_right (hVU f) }
  change @MeasurableSet C(X, Y) m s
  rw [heq]
  exact MeasurableSet.biUnion htc (fun f _ ↦ hclosed K (closure (V f)) isClosed_closure)
