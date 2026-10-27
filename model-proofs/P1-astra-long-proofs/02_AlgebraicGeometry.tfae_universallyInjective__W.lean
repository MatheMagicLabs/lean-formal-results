/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     AlgebraicGeometry.tfae_universallyInjective
Source:      Mathlib @ d0a050ad6, Mathlib/AlgebraicGeometry/Morphisms/UniversallyInjective.lean, line 107
             (added after the model's training data; human proof 51 tactic steps)
Experiment:  P1-astra-long-proofs, arm W, solved after 2 call(s)
Prover:      gpt-6-astra
Setup:       GPT-6 Astra (Codex, effort medium), at most 10 calls per theorem: W = whole proof plus repair rounds;
             WT = W with read-only Mathlib sources to search; P = Lean-checked skeleton of have-steps, then one step per call
Check:       the proof replaced the human proof in the Mathlib file above; Lean reported
             0 errors and no `sorry`.
-/

theorem tfae_universallyInjective :
    List.TFAE [
      UniversallyInjective f,
      ∀ (K : Type u) [Field K], Function.Injective (fun g : Spec (.of K) ⟶ X ↦ g ≫ f),
      Function.Injective f ∧ ∀ x, (f.residueFieldMap x).hom.IsPurelyInseparable,
      Surjective (pullback.diagonal f) ] := by
  tfae_have 1 ↔ 4 := UniversallyInjective.iff_diagonal f
  tfae_have 3 → 2 := by {
  intro ⟨h_inj, hf⟩ K _ g₁ g₂ hg
  obtain ⟨e, h⟩ := Scheme.SpecToEquivOfField_eq_iff.mp congr(Y.SpecToEquivOfField K $hg)
  apply (X.SpecToEquivOfField K).injective
  dsimp at e h
  simp only [Scheme.descResidueField_stalkClosedPointTo_comp] at e h
  rw [← f.residueFieldMap_congr'_assoc (h_inj e), CommRingCat.hom_ext_iff] at h
  rw [Scheme.SpecToEquivOfField_eq_iff]
  let x := g₁ (IsLocalRing.closedPoint K)
  have hfx := hf x
  algebraize [(f.residueFieldMap (g₁ (IsLocalRing.closedPoint K))).hom]
  refine ⟨h_inj e, CommRingCat.hom_ext ?_⟩
  exact IsPurelyInseparable.injective_comp_algebraMap (Y.residueField (f x)) (X.residueField x) _ h }
  tfae_have 2 → 4 := by {
  intro h
  rw [surjective_iff]
  intro z
  let φ := (pullback f f).fromSpecResidueField z
  have hφ₁ : φ ≫ pullback.fst f f = φ ≫ pullback.snd f f :=
  h ((pullback f f).residueField z) (by simp [pullback.condition])
  have hφ₂ : φ = (φ ≫ pullback.fst f f) ≫ pullback.diagonal f := by {
  apply pullback.hom_ext <;> simp [Category.assoc, hφ₁] }
  refine ⟨(φ ≫ pullback.fst f f) (IsLocalRing.closedPoint _), ?_⟩
  rw [← Scheme.Hom.comp_apply, ← hφ₂, Scheme.fromSpecResidueField_apply] }
  tfae_have 4 → 3 := by {
  intro hf
  have := tfae_1_iff_4.mpr hf
  refine ⟨f.injective, ?_⟩
  rw [surjective_iff] at hf
  intro x
  algebraize [(f.residueFieldMap x).hom]
  rw [RingHom.IsPurelyInseparable, isPurelyInseparable_iff_subsingleton_emb, subsingleton_iff]
  intro σ₁ σ₂
  suffices hσ : σ₁.toRingHom = σ₂.toRingHom by {
  ext a
  exact DFunLike.congr_fun hσ a }
  let g₁ := (X.SpecToEquivOfField _).symm ⟨_, CommRingCat.ofHom σ₁.toRingHom⟩
  let g₂ := (X.SpecToEquivOfField _).symm ⟨_, CommRingCat.ofHom σ₂.toRingHom⟩
  suffices X.SpecToEquivOfField _ g₁ = X.SpecToEquivOfField _ g₂ by {
  rw [Equiv.apply_symm_apply, Equiv.apply_symm_apply] at this
  congrm $(this).2.hom }
  let q := pullback.lift (f := f) (g := f) g₁ g₂ (by {
  simp only [g₁, g₂, Scheme.SpecToEquivOfField_symm_apply, AlgHom.toRingHom_eq_coe,
  Category.assoc, ← f.SpecMap_residueFieldMap_fromSpecResidueField x, ← Spec.map_comp_assoc]
  congr 2
  ext a
  simp only [CommRingCat.hom_comp, RingHom.comp_apply]
  exact (AlgHom.commutes σ₁ a).trans (AlgHom.commutes σ₂ a).symm })
  have q_fst : q ≫ pullback.fst f f = g₁ := pullback.lift_fst _ _ _
  have q_snd : q ≫ pullback.snd f f = g₂ := pullback.lift_snd _ _ _
  rw [Scheme.SpecToEquivOfField_eq_iff, ← q_fst, ← q_snd]
  obtain ⟨u, hu⟩ := hf (q (IsLocalRing.closedPoint _))
  have hux : u = x := by {
  have := congr(pullback.fst f f $hu)
  rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply] at this
  simpa [Scheme.SpecToEquivOfField_symm_apply, q_fst, g₁] using this }
  refine ⟨by simp [g₁, g₂, q_fst, q_snd], ?_⟩
  dsimp
  simp only [Scheme.descResidueField_stalkClosedPointTo_comp, ← Category.assoc]
  congr 1
  rw [← cancel_mono (Scheme.residueFieldCongr (hux ▸ hu).symm).hom]
  have : Mono (Scheme.Hom.residueFieldMap (pullback.diagonal f) x) :=
  ConcreteCategory.mono_of_injective _ (RingHom.injective _)
  simp [← cancel_mono ((pullback.diagonal f).residueFieldMap x), ← Scheme.residueFieldMap_comp,
  (pullback.fst f f).residueFieldMap_congr', (pullback.snd f f).residueFieldMap_congr'_assoc,
  Scheme.Hom.residueFieldMap_congr (pullback.diagonal_snd f),
  Scheme.Hom.residueFieldMap_congr (pullback.diagonal_fst f)] }
  tfae_finish
