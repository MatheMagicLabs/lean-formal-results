/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     ContinuousMap.borel_eq_iSup_comap_eval
Source:      Mathlib @ d0a050ad6, Mathlib/MeasureTheory/Constructions/BorelSpace/ContinuousMap.lean, line 77
             (added after the model's training data; human proof 37 tactic steps)
Experiment:  P1-astra-long-proofs, arm W, solved after 4 call(s)
Prover:      gpt-6-astra
Setup:       GPT-6 Astra (Codex, effort medium), at most 10 calls per theorem: W = whole proof plus repair rounds;
             WT = W with read-only Mathlib sources to search; P = Lean-checked skeleton of have-steps, then one step per call
Check:       the proof replaced the human proof in the Mathlib file above; Lean reported
             0 errors and no `sorry`.
-/

theorem borel_eq_iSup_comap_eval :
    borel C(X, Y) = ⨆ x : X, (borel Y).comap fun f ↦ f x := by
  borelize Y
  apply le_antisymm _ iSup_comap_le_borel
  let m : MeasurableSpace C(X, Y) :=
    ⨆ x : X, (borel Y).comap (fun f : C(X, Y) ↦ f x)
  letI : MeasurableSpace C(X, Y) := m
  have heval (x : X) : Measurable (fun f : C(X, Y) ↦ f x) := by {
  apply measurable_iff_comap_le.mpr
  change (borel Y).comap (fun f : C(X, Y) ↦ f x) ≤
    ⨆ z : X, (borel Y).comap (fun f : C(X, Y) ↦ f z)
  exact le_iSup (fun z : X ↦ (borel Y).comap (fun f : C(X, Y) ↦ f z)) x }
  have hclosed (K : Set X) (F : Set Y) (hF : IsClosed F) :
      MeasurableSet {f : C(X, Y) | Set.MapsTo f K F} := by {
  obtain ⟨D, hDc, hDd⟩ := exists_countable_dense K
  have heq : {f : C(X, Y) | Set.MapsTo f K F} =
      ⋂ x ∈ D, {f : C(X, Y) | f (x : X) ∈ F} := by {
  ext f
  simp only [Set.mem_setOf_eq, Set.mem_iInter]
  constructor
  · exact fun hf x _ ↦ hf x.property
  · intro hf x hx
    have hsub : D ⊆ {z : K | f (z : X) ∈ F} := hf
    have hc : IsClosed {z : K | f (z : X) ∈ F} :=
      hF.preimage (f.continuous.comp continuous_subtype_val)
    have h := closure_minimal hsub hc
    rw [hDd.closure_eq] at h
    exact h (Set.mem_univ (⟨x, hx⟩ : K)) }
  rw [heq]
  exact MeasurableSet.biInter hDc (fun x _ ↦ hF.measurableSet.preimage (heval x)) }
  obtain ⟨b, hbc, _, hb⟩ := exists_countable_basis Y
  letI : Countable b := hbc.to_subtype
  have hopen (K : Set X) (U : Set Y) (hK : IsCompact K) (hU : IsOpen U) :
      MeasurableSet {f : C(X, Y) | Set.MapsTo f K U} := by {
  let I := {V : b // closure (V : Set Y) ⊆ U}
  let F (t : Finset I) : Set Y := ⋃ V ∈ t, closure (V.val : Set Y)
  have hFc (t : Finset I) : IsClosed (F t) := by {
  exact isClosed_biUnion_finset (fun _ _ ↦ isClosed_closure) }
  have hFU (t : Finset I) : F t ⊆ U := by {
  intro y hy
  obtain ⟨V, hV, hyV⟩ := Set.mem_iUnion₂.mp hy
  exact V.property hyV }
  have heq : {f : C(X, Y) | Set.MapsTo f K U} =
      ⋃ t : Finset I, {f : C(X, Y) | Set.MapsTo f K (F t)} := by {
  ext f
  simp only [Set.mem_setOf_eq, Set.mem_iUnion]
  constructor
  · intro hf
    have hcover : K ⊆ ⋃ V : I, f ⁻¹' (V.val : Set Y) := by {
    intro x hx
    obtain ⟨A, hA, hAc, hAU⟩ :=
      exists_mem_nhds_isClosed_subset (hU.mem_nhds (hf hx))
    obtain ⟨V, hVb, hxV, hVA⟩ := hb.mem_nhds_iff.mp hA
    let V' : I := ⟨⟨V, hVb⟩, (closure_minimal hVA hAc).trans hAU⟩
    exact Set.mem_iUnion.mpr ⟨V', hxV⟩ }
    obtain ⟨t, ht⟩ := hK.elim_finite_subcover
      (fun V : I ↦ f ⁻¹' (V.val : Set Y))
      (fun V ↦ (hb.isOpen V.val.property).preimage f.continuous) hcover
    refine ⟨t, ?_⟩
    intro x hx
    obtain ⟨V, hV, hxV⟩ := Set.mem_iUnion₂.mp (ht hx)
    exact Set.mem_iUnion₂.mpr ⟨V, hV, subset_closure hxV⟩
  · rintro ⟨t, ht⟩ x hx
    exact hFU t (ht hx) }
  rw [heq]
  exact MeasurableSet.iUnion (fun t ↦ hclosed K (F t) (hFc t)) }
  have htop := compactOpen_eq_generateFrom
    (fun (K : Set X) (hK : K ∈ {K : Set X | IsCompact K}) ↦ hK) hb
    (by {
    intro f x V hV hx
    obtain ⟨K, hKn, hKV, hKc⟩ :=
      LocallyCompactSpace.local_compact_nhds x (f ⁻¹' V)
        (((hb.isOpen hV).preimage f.continuous).mem_nhds hx)
    exact ⟨K, hKc, hKn, hKV⟩ })
  rw [borel_eq_generateFrom_of_subbasis htop]
  apply MeasurableSpace.generateFrom_le
  rintro s ⟨K, hK, t, ht, rfl⟩
  exact hopen K (⋃₀ t) hK (isOpen_sUnion (fun U hU ↦ hb.isOpen (ht.2 hU)))
