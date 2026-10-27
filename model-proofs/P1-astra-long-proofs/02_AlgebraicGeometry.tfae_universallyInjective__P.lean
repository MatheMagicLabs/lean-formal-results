/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     AlgebraicGeometry.tfae_universallyInjective
Source:      Mathlib @ d0a050ad6, Mathlib/AlgebraicGeometry/Morphisms/UniversallyInjective.lean, line 107
             (added after the model's training data; human proof 51 tactic steps)
Experiment:  P1-astra-long-proofs, arm P, solved after 7 call(s)
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
  have h12 : UniversallyInjective f →
      ∀ (K : Type u) [Field K], Function.Injective (fun g : Spec (.of K) ⟶ X ↦ g ≫ f) := by
    intro hf K _ g₁ g₂ hg
    let q := pullback.lift (f := f) (g := f) g₁ g₂ hg
    have q_fst : q ≫ pullback.fst f f = g₁ := pullback.lift_fst _ _ _
    have q_snd : q ≫ pullback.snd f f = g₂ := pullback.lift_snd _ _ _
    have hd := (UniversallyInjective.iff_diagonal f).mp hf
    rw [surjective_iff] at hd
    obtain ⟨u, hu⟩ := hd (q (IsLocalRing.closedPoint K))
    have hu₁ : pullback.fst f f (q (IsLocalRing.closedPoint K)) = u := by
      rw [← hu, ← Scheme.Hom.comp_apply, pullback.diagonal_fst]
      rfl
    have hu₂ : pullback.snd f f (q (IsLocalRing.closedPoint K)) = u := by
      rw [← hu, ← Scheme.Hom.comp_apply, pullback.diagonal_snd]
      rfl
    apply (X.SpecToEquivOfField K).injective
    rw [Scheme.SpecToEquivOfField_eq_iff, ← q_fst, ← q_snd]
    refine ⟨?_, ?_⟩
    · change (q ≫ pullback.fst f f) (IsLocalRing.closedPoint K) =
        (q ≫ pullback.snd f f) (IsLocalRing.closedPoint K)
      simpa only [Scheme.Hom.comp_apply] using hu₁.trans hu₂.symm
    · dsimp
      simp only [Scheme.descResidueField_stalkClosedPointTo_comp, ← Category.assoc]
      congr 1
      rw [← cancel_mono (Scheme.residueFieldCongr hu.symm).hom]
      have : Mono (Scheme.Hom.residueFieldMap (pullback.diagonal f) u) :=
        ConcreteCategory.mono_of_injective _ (RingHom.injective _)
      simp [← cancel_mono ((pullback.diagonal f).residueFieldMap u),
        ← Scheme.residueFieldMap_comp,
        (pullback.fst f f).residueFieldMap_congr',
        (pullback.snd f f).residueFieldMap_congr'_assoc,
        Scheme.Hom.residueFieldMap_congr (pullback.diagonal_snd f),
        Scheme.Hom.residueFieldMap_congr (pullback.diagonal_fst f)]
  have h23 : (∀ (K : Type u) [Field K],
      Function.Injective (fun g : Spec (.of K) ⟶ X ↦ g ≫ f)) →
      Function.Injective f ∧ ∀ x, (f.residueFieldMap x).hom.IsPurelyInseparable := by
    intro h
    have hd : Surjective (pullback.diagonal f) := by
      rw [surjective_iff]
      intro z
      let φ := (pullback f f).fromSpecResidueField z
      have he : φ ≫ pullback.fst f f = φ ≫ pullback.snd f f :=
        h ((pullback f f).residueField z) (by simp [pullback.condition])
      have he' : φ = (φ ≫ pullback.fst f f) ≫ pullback.diagonal f := by
        cat_disch
      refine ⟨(φ ≫ pullback.fst f f) (IsLocalRing.closedPoint _), ?_⟩
      rw [← Scheme.Hom.comp_apply, ← he', Scheme.fromSpecResidueField_apply]
    letI : UniversallyInjective f := (UniversallyInjective.iff_diagonal f).mpr hd
    refine ⟨f.injective, ?_⟩
    intro x
    algebraize [(f.residueFieldMap x).hom]
    rw [RingHom.IsPurelyInseparable, isPurelyInseparable_iff_subsingleton_emb,
      subsingleton_iff]
    intro σ₁ σ₂
    suffices σ₁.toRingHom = σ₂.toRingHom by
      ext a
      exact congrArg (fun ψ => ψ a) this
    let g₁ := (X.SpecToEquivOfField _).symm ⟨x, CommRingCat.ofHom σ₁.toRingHom⟩
    let g₂ := (X.SpecToEquivOfField _).symm ⟨x, CommRingCat.ofHom σ₂.toRingHom⟩
    suffices X.SpecToEquivOfField _ g₁ = X.SpecToEquivOfField _ g₂ by
      rw [Equiv.apply_symm_apply, Equiv.apply_symm_apply] at this
      congrm $(this).2.hom
    apply congrArg (X.SpecToEquivOfField _)
    apply h _
    simp only [g₁, g₂, Scheme.SpecToEquivOfField_symm_apply, AlgHom.toRingHom_eq_coe,
      Category.assoc, ← f.SpecMap_residueFieldMap_fromSpecResidueField x,
      ← Spec.map_comp_assoc]
    congr 2
    ext a
    simp only [CommRingCat.hom_comp, RingHom.comp_apply]
    exact (AlgHom.commutes σ₁ a).trans (AlgHom.commutes σ₂ a).symm
  have h31 : (Function.Injective f ∧
      ∀ x, (f.residueFieldMap x).hom.IsPurelyInseparable) → UniversallyInjective f := by
    rintro ⟨hinj, hres⟩
    have hField : ∀ (K : Type u) [Field K],
        Function.Injective (fun g : Spec (.of K) ⟶ X ↦ g ≫ f) := by
      intro K _ g₁ g₂ hg
      obtain ⟨e, h⟩ :=
        Scheme.SpecToEquivOfField_eq_iff.mp congr(Y.SpecToEquivOfField K $hg)
      apply (X.SpecToEquivOfField K).injective
      dsimp at e h
      simp only [Scheme.descResidueField_stalkClosedPointTo_comp] at e h
      rw [← f.residueFieldMap_congr'_assoc (hinj e), CommRingCat.hom_ext_iff] at h
      rw [Scheme.SpecToEquivOfField_eq_iff]
      let x := g₁ (IsLocalRing.closedPoint K)
      have hx := hres x
      algebraize [(f.residueFieldMap (g₁ (IsLocalRing.closedPoint K))).hom]
      refine ⟨hinj e, CommRingCat.hom_ext ?_⟩
      exact IsPurelyInseparable.injective_comp_algebraMap
        (Y.residueField (f x)) (X.residueField x) _ h
    apply (UniversallyInjective.iff_diagonal f).mpr
    rw [surjective_iff]
    intro z
    let φ := (pullback f f).fromSpecResidueField z
    have he : φ ≫ pullback.fst f f = φ ≫ pullback.snd f f :=
      hField ((pullback f f).residueField z) (by simp [pullback.condition])
    have he' : φ = (φ ≫ pullback.fst f f) ≫ pullback.diagonal f := by
      cat_disch
    refine ⟨(φ ≫ pullback.fst f f) (IsLocalRing.closedPoint _), ?_⟩
    rw [← Scheme.Hom.comp_apply, ← he', Scheme.fromSpecResidueField_apply]
  tfae_have 1 → 2 := h12
  tfae_have 2 → 3 := h23
  tfae_have 3 → 1 := h31
  tfae_have 1 ↔ 4 := UniversallyInjective.iff_diagonal f
  tfae_finish
