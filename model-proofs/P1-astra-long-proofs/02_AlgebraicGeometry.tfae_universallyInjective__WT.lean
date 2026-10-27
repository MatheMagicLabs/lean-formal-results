/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     AlgebraicGeometry.tfae_universallyInjective
Source:      Mathlib @ d0a050ad6, Mathlib/AlgebraicGeometry/Morphisms/UniversallyInjective.lean, line 107
             (added after the model's training data; human proof 51 tactic steps)
Experiment:  P1-astra-long-proofs, arm WT, solved after 4 call(s)
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
  classical
  have sections : ∀ (K : Type u) [Field K] (P : Scheme.{u}) (q : P ⟶ Spec (.of K)), Injective q → ∀ s t : Spec (.of K) ⟶ P, s ≫ q = 𝟙 _ → t ≫ q = 𝟙 _ → s = t := by {
  intro K _ P q hq s t hs ht
  obtain ⟨⟨x, a⟩, rfl⟩ := (Scheme.SpecToEquivOfField K P).symm.surjective s
  obtain ⟨⟨y, b⟩, rfl⟩ := (Scheme.SpecToEquivOfField K P).symm.surjective t
  change (Spec.map a ≫ P.fromSpecResidueField x) ≫ q = 𝟙 _ at hs
  change (Spec.map b ≫ P.fromSpecResidueField y) ≫ q = 𝟙 _ at ht
  change Spec.map a ≫ P.fromSpecResidueField x = Spec.map b ≫ P.fromSpecResidueField y
  have e : x = y := hq (Subsingleton.elim _ _)
  subst y
  let c := Spec.preimage (P.fromSpecResidueField x ≫ q)
  have ha : c ≫ a = 𝟙 _ := by {
  apply Spec.map_injective
  simpa only [Spec.map_comp, Spec.map_preimage, Spec.map_id, Category.assoc, c] using hs }
  have hb : c ≫ b = 𝟙 _ := by {
  apply Spec.map_injective
  simpa only [Spec.map_comp, Spec.map_preimage, Spec.map_id, Category.assoc, c] using ht }
  haveI : Mono a := ConcreteCategory.mono_of_injective a a.hom.injective
  have hac : a ≫ c = 𝟙 _ := by {
  apply (cancel_mono a).mp
  simp [Category.assoc, ha] }
  have hab : a = b := by {
  calc
  a = a ≫ (c ≫ b) := by rw [hb, Category.comp_id]
  _ = (a ≫ c) ≫ b := (Category.assoc _ _ _).symm
  _ = b := by rw [hac, Category.id_comp] }
  rw [hab] }
  have h12 : UniversallyInjective f → ∀ (K : Type u) [Field K], Injective (fun g : Spec (.of K) ⟶ X ↦ g ≫ f) := by {
  intro hf K _ g₁ g₂ e
  let q := pullback.snd f (g₁ ≫ f)
  let s : Spec (.of K) ⟶ pullback f (g₁ ≫ f) := pullback.lift g₁ (𝟙 _) (by simp)
  let t : Spec (.of K) ⟶ pullback f (g₁ ≫ f) := pullback.lift g₂ (𝟙 _) (by simpa using e.symm)
  have hq : Injective q := hf.1 _ _ _ (IsPullback.of_hasPullback f (g₁ ≫ f)).flip
  have hst : s = t := sections K _ q hq s t (by simp [s, q]) (by simp [t, q])
  simpa [s, t] using congrArg (fun k ↦ k ≫ pullback.fst f (g₁ ≫ f)) hst }
  have h24 : (∀ (K : Type u) [Field K], Injective (fun g : Spec (.of K) ⟶ X ↦ g ≫ f)) → Surjective (pullback.diagonal f) := by {
  intro h
  constructor
  intro p
  let r := (pullback f f).fromSpecResidueField p
  have e : r ≫ pullback.fst f f = r ≫ pullback.snd f f := h ((pullback f f).residueField p) (by simp only [Category.assoc, pullback.condition])
  have hh : (r ≫ pullback.fst f f) ≫ pullback.diagonal f = r := by {
  apply pullback.hom_ext
  · simp only [Category.assoc, pullback.diagonal_fst, Category.comp_id]
  · simpa only [Category.assoc, pullback.diagonal_snd, Category.comp_id] using e }
  refine ⟨pullback.fst f f p, ?_⟩
  simpa [r, Scheme.Hom.comp_apply] using congrArg (fun k ↦ k (IsLocalRing.closedPoint ((pullback f f).residueField p))) hh }
  have h23 : (∀ (K : Type u) [Field K], Injective (fun g : Spec (.of K) ⟶ X ↦ g ≫ f)) → Injective f ∧ ∀ x, (f.residueFieldMap x).hom.IsPurelyInseparable := by {
  intro h
  haveI : UniversallyInjective f := (UniversallyInjective.iff_diagonal f).mpr (h24 h)
  refine ⟨f.injective, ?_⟩
  intro x
  letI := (f.residueFieldMap x).hom.toAlgebra
  letI : Nonempty (X.residueField x →+* AlgebraicClosure (X.residueField x)) := ⟨algebraMap (X.residueField x) (AlgebraicClosure (X.residueField x))⟩
  change IsPurelyInseparable (Y.residueField (f x)) (X.residueField x)
  apply IsPurelyInseparable.of_injective_comp_algebraMap (Y.residueField (f x)) (X.residueField x) (AlgebraicClosure (X.residueField x))
  intro a b hab
  have e : CommRingCat.ofHom a = CommRingCat.ofHom b := by {
  apply Spec.map_injective
  apply (cancel_mono (X.fromSpecResidueField x)).mp
  apply h (AlgebraicClosure (X.residueField x))
  have hc : f.residueFieldMap x ≫ CommRingCat.ofHom a = f.residueFieldMap x ≫ CommRingCat.ofHom b := CommRingCat.hom_ext hab
  have he := congrArg (fun k ↦ Spec.map k ≫ Y.fromSpecResidueField (f x)) hc
  simpa only [Spec.map_comp, Category.assoc, Scheme.Hom.SpecMap_residueFieldMap_fromSpecResidueField] using! he }
  exact congrArg CommRingCat.Hom.hom e }
  have h32 : (Injective f ∧ ∀ x, (f.residueFieldMap x).hom.IsPurelyInseparable) → ∀ (K : Type u) [Field K], Injective (fun g : Spec (.of K) ⟶ X ↦ g ≫ f) := by {
  rintro ⟨hi, hp⟩ K _ g₁ g₂ e
  obtain ⟨⟨x, a⟩, rfl⟩ := (Scheme.SpecToEquivOfField K X).symm.surjective g₁
  obtain ⟨⟨y, b⟩, rfl⟩ := (Scheme.SpecToEquivOfField K X).symm.surjective g₂
  change (Spec.map a ≫ X.fromSpecResidueField x) ≫ f = (Spec.map b ≫ X.fromSpecResidueField y) ≫ f at e
  change Spec.map a ≫ X.fromSpecResidueField x = Spec.map b ≫ X.fromSpecResidueField y
  have hxy : f x = f y := by {
  simpa [Scheme.Hom.comp_apply] using congrArg (fun k ↦ k (IsLocalRing.closedPoint K)) e }
  have hxy' := hi hxy
  subst y
  have hab : f.residueFieldMap x ≫ a = f.residueFieldMap x ≫ b := by {
  apply Spec.map_injective
  apply (cancel_mono (Y.fromSpecResidueField (f x))).mp
  simpa only [Spec.map_comp, Category.assoc, Scheme.Hom.SpecMap_residueFieldMap_fromSpecResidueField] using e }
  letI := (f.residueFieldMap x).hom.toAlgebra
  haveI : IsPurelyInseparable (Y.residueField (f x)) (X.residueField x) := hp x
  have hab' : a.hom = b.hom := IsPurelyInseparable.injective_comp_algebraMap (Y.residueField (f x)) (X.residueField x) K (congrArg CommRingCat.Hom.hom hab)
  rw [CommRingCat.hom_ext hab'] }
  tfae_have 1 → 2 := h12
  tfae_have 2 → 3 := h23
  tfae_have 3 → 2 := h32
  tfae_have 2 → 4 := h24
  tfae_have 1 ↔ 4 := UniversallyInjective.iff_diagonal f
  tfae_finish
