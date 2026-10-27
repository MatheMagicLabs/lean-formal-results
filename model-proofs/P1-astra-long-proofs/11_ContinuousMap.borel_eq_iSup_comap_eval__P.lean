/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     ContinuousMap.borel_eq_iSup_comap_eval
Source:      Mathlib @ d0a050ad6, Mathlib/MeasureTheory/Constructions/BorelSpace/ContinuousMap.lean, line 77
             (added after the model's training data; human proof 37 tactic steps)
Experiment:  P1-astra-long-proofs, arm P, solved after 7 call(s)
Prover:      gpt-6-astra
Setup:       GPT-6 Astra (Codex, effort medium), at most 10 calls per theorem: W = whole proof plus repair rounds;
             WT = W with read-only Mathlib sources to search; P = Lean-checked skeleton of have-steps, then one step per call
Check:       the proof replaced the human proof in the Mathlib file above; Lean reported
             0 errors and no `sorry`.
-/

theorem borel_eq_iSup_comap_eval :
    borel C(X, Y) = ⨆ x : X, (borel Y).comap fun f ↦ f x := by
  have hBorel_le : borel C(X, Y) ≤ ⨆ x : X, (borel Y).comap (fun f : C(X, Y) ↦ f x) := by
    classical
    borelize Y
    let m : MeasurableSpace C(X, Y) :=
      ⨆ x : X, (borel Y).comap (fun f : C(X, Y) ↦ f x)
    have hEval (x : X) : @Measurable C(X, Y) Y m (borel Y) (fun f ↦ f x) := by
      apply measurable_iff_comap_le.mpr
      change (borel Y).comap (fun f : C(X, Y) ↦ f x) ≤
        ⨆ z : X, (borel Y).comap (fun f : C(X, Y) ↦ f z)
      exact le_iSup (fun z : X ↦ (borel Y).comap (fun f : C(X, Y) ↦ f z)) x
    have hClosed (K : Set X) (F : Set Y) (hF : IsClosed F) :
        @MeasurableSet C(X, Y) m {f | Set.MapsTo f K F} := by
      obtain ⟨D, hDc, hDd⟩ := exists_countable_dense K
      have heq :
          {f : C(X, Y) | Set.MapsTo f K F} =
            ⋂ x ∈ D, {f : C(X, Y) | f (x : X) ∈ F} := by
        ext f
        simp only [Set.mem_setOf_eq, Set.mem_iInter]
        constructor
        · intro hf x hx
          exact hf x.property
        · intro hf x hx
          have hp : IsClosed {z : K | f (z : X) ∈ F} :=
            hF.preimage (f.continuous.comp continuous_subtype_val)
          have hs : closure D ⊆ {z : K | f (z : X) ∈ F} :=
            closure_minimal hf hp
          rw [hDd.closure_eq] at hs
          exact hs (Set.mem_univ (⟨x, hx⟩ : K))
      rw [heq]
      exact MeasurableSet.biInter hDc (fun x _ ↦ hEval x hF.measurableSet)
    obtain ⟨B, hBc, hBempty, hB⟩ := exists_countable_basis Y
    letI := hBc.toEncodable
    have hOpen (K : Set X) (hK : IsCompact K) (U : Set Y) (hU : IsOpen U) :
        @MeasurableSet C(X, Y) m {f | Set.MapsTo f K U} := by
      let I := {V : B // closure (V : Set Y) ⊆ U}
      let F (s : Finset I) : Set Y := ⋃ V ∈ s, closure (V.val : Set Y)
      have hFc (s : Finset I) : IsClosed (F s) :=
        isClosed_biUnion_finset (fun V _ ↦ isClosed_closure)
      have hFU (s : Finset I) : F s ⊆ U := by
        intro y hy
        obtain ⟨V, _, hy⟩ := Set.mem_iUnion₂.mp hy
        exact V.property hy
      have heq :
          {f : C(X, Y) | Set.MapsTo f K U} =
            ⋃ s : Finset I, {f : C(X, Y) | Set.MapsTo f K (F s)} := by
        ext f
        simp only [Set.mem_setOf_eq, Set.mem_iUnion]
        constructor
        · intro hf
          have hcover : f '' K ⊆ ⋃ V : I, (V.val : Set Y) := by
            rintro y ⟨x, hx, rfl⟩
            obtain ⟨A, hAn, hAc, hAU⟩ :=
              exists_mem_nhds_isClosed_subset (hU.mem_nhds (hf hx))
            obtain ⟨W, hWA, hWo, hxW⟩ := mem_nhds_iff.mp hAn
            have hWU : closure W ⊆ U :=
              (closure_minimal hWA hAc).trans hAU
            obtain ⟨V, hVB, hxV, hVW⟩ := hB.exists_subset_of_mem_open hxW hWo
            let v : I := ⟨⟨V, hVB⟩, (closure_mono hVW).trans hWU⟩
            exact Set.mem_iUnion.mpr ⟨v, hxV⟩
          obtain ⟨s, hs⟩ := (hK.image f.continuous).elim_finite_subcover
            (fun V : I ↦ (V.val : Set Y))
            (fun V ↦ hB.isOpen V.val.property) hcover
          refine ⟨s, ?_⟩
          intro x hx
          obtain ⟨V, hVs, hxV⟩ := Set.mem_iUnion₂.mp (hs ⟨x, hx, rfl⟩)
          exact Set.mem_iUnion₂.mpr ⟨V, hVs, subset_closure hxV⟩
        · rintro ⟨s, hs⟩ x hx
          exact hFU s (hs hx)
      rw [heq]
      exact MeasurableSet.iUnion (fun s ↦ hClosed K (F s) (hFc s))
    have htop :
        (inferInstance : TopologicalSpace C(X, Y)) =
          TopologicalSpace.generateFrom
            (Set.image2
              (fun (K : Set X) (t : Set (Set Y)) ↦
                {f : C(X, Y) | Set.MapsTo f K (⋃₀ t)})
              {K : Set X | IsCompact K} {t | t.Finite ∧ t ⊆ B}) := by
      apply ContinuousMap.compactOpen_eq_generateFrom
      · intro K hK
        exact hK
      · exact hB
      · intro f x V hV hx
        obtain ⟨K, hK, hxK, hKV⟩ :=
          exists_compact_subset ((hB.isOpen hV).preimage f.continuous) hx
        exact ⟨K, hK, mem_interior_iff_mem_nhds.mp hxK, hKV⟩
    rw [borel_eq_generateFrom_of_subbasis htop]
    refine MeasurableSpace.generateFrom_le ?_
    rintro s ⟨K, hK, t, ht, rfl⟩
    exact hOpen K hK (⋃₀ t) (isOpen_sUnion (fun V hV ↦ hB.isOpen (ht.2 hV)))
  exact le_antisymm hBorel_le ContinuousMap.iSup_comap_le_borel
