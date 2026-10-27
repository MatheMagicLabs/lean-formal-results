/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     CategoryTheory.MorphismProperty.sourceLocalClosure.sourceLocalClosure_iff_of_respectsLeft
Source:      Mathlib @ d0a050ad6, Mathlib/CategoryTheory/MorphismProperty/LocalClosure.lean, line 94
             (added after the model's training data; human proof 35 tactic steps)
Experiment:  P1-astra-long-proofs, arm WT, solved after 3 call(s)
Prover:      gpt-6-astra
Setup:       GPT-6 Astra (Codex, effort medium), at most 10 calls per theorem: W = whole proof plus repair rounds;
             WT = W with read-only Mathlib sources to search; P = Lean-checked skeleton of have-steps, then one step per call
Check:       the proof replaced the human proof in the Mathlib file above; Lean reported
             0 errors and no `sorry`.
-/

lemma sourceLocalClosure_iff_of_respectsLeft [P.RespectsIso] [P.RespectsLeft K.morphismProperty]
    [K.HasIsos] [K.IsStableUnderBaseChange] [K.IsStableUnderComposition] [K.HasPullbacks] {X Y : C}
    {f : X ⟶ Y} :
    sourceLocalClosure K P f ↔ ∃ R ∈ K X, ∀ (U : C) (g : U ⟶ X), R g → P (g ≫ f) := by
  classical
  have H : ∀ {X Y : C} {f : X ⟶ Y}, sourceLocalClosure K P f → ∃ E : K.ZeroHypercover.{max u v} X, ∀ i, P (E.f i ≫ f) := by {
  intro X Y f hf
  induction hf with
  | of f hf => {
  refine ⟨.singleton (𝟙 _) (K.mem_coverings_of_isIso _), ?_⟩
  intro i
  simpa using hf }
  | of_iso f g e hf ih => {
  obtain ⟨E, hE⟩ := ih
  refine ⟨E.pushforward e.hom.left (K.mem_coverings_of_isIso _), ?_⟩
  change ∀ i : E.I₀, P ((E.f i ≫ e.hom.left) ≫ g)
  intro i
  have hw : e.hom.left ≫ g = f ≫ e.hom.right := e.hom.w
  rw [Category.assoc, hw, ← Category.assoc]
  exact RespectsIso.postcomp P e.hom.right _ (hE i) }
  | comp f hf R hR g hg ih => {
  obtain ⟨E, hE⟩ := ih
  refine ⟨E.pullback₁ g, ?_⟩
  change ∀ i : E.I₀, P (pullback.fst g (E.f i) ≫ (g ≫ f))
  intro i
  rw [← Category.assoc, pullback.condition, Category.assoc]
  letI : R.HasPullbacks (E.f i) := K.hasPullbacks_of_mem _ hR
  exact RespectsLeft.precomp (P := P) (Q := K.morphismProperty) _ ⟨R.pullbackArrows (E.f i), K.pullbackArrows_mem _ hR, Presieve.pullbackArrows.mk _ _ hg⟩ _ (hE i) }
  | of_presieve f R hR h ih => {
  obtain ⟨E, rfl⟩ := Precoverage.mem_iff_exists_zeroHypercover.mp hR
  have hh := fun i ↦ ih _ (E.f i) (Presieve.ofArrows.mk i)
  choose F hF using hh
  refine ⟨E.bind F, ?_⟩
  change ∀ i : (Σ j : E.I₀, (F j).I₀), P (((F i.1).f i.2 ≫ E.f i.1) ≫ f)
  intro i
  simpa only [Category.assoc] using hF i.1 i.2 } }
  constructor
  · {
  intro hf
  obtain ⟨E, hE⟩ := H hf
  refine ⟨E.presieve₀, E.mem₀, ?_⟩
  rintro U g ⟨i⟩
  exact hE i }
  · {
  rintro ⟨R, hR, h⟩
  exact .of_presieve _ R hR (fun U g hg ↦ .of _ (h U g hg)) }
