/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     CategoryTheory.MorphismProperty.sourceLocalClosure.sourceLocalClosure_iff_of_respectsLeft
Source:      Mathlib @ d0a050ad6, Mathlib/CategoryTheory/MorphismProperty/LocalClosure.lean, line 94
             (added after the model's training data; human proof 35 tactic steps)
Experiment:  P1-astra-long-proofs, arm W, solved after 3 call(s)
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
  refine ⟨?_, fun ⟨R,hR,h⟩ ↦ .of_presieve _ R hR (fun U g hg ↦ .of _ (h U g hg))⟩
  intro hf
  induction hf with
  | of f hf => exact ⟨.singleton (𝟙 _), K.mem_coverings_of_isIso _, fun U g ⟨⟩ ↦ by simpa⟩
  | of_iso f g e hf ih => {
  obtain ⟨R,hR,h⟩ := ih
  rw [K.mem_iff_exists_zeroHypercover] at hR
  obtain ⟨E,rfl⟩ := hR
  refine ⟨_, (E.pushforward e.hom.left (K.mem_coverings_of_isIso _)).mem₀, ?_⟩
  rintro U v ⟨i⟩
  dsimp
  simp only [Category.assoc, Arrow.w_mk_right, Arrow.mk_left, Arrow.mk_right, Arrow.mk_hom]
  rw [← Category.assoc, P.cancel_right_of_respectsIso]
  exact h _ _ ⟨i⟩ }
  | comp f hf R hR g hg ih => {
  obtain ⟨S,hS,h⟩ := ih
  rw [K.mem_iff_exists_zeroHypercover] at hS hR
  obtain ⟨E,rfl⟩ := hS
  obtain ⟨F,rfl⟩ := hR
  refine ⟨(E.pullback₁ g).presieve₀, (E.pullback₁ g).mem₀, ?_⟩
  rintro U v ⟨i⟩
  dsimp
  rw [pullback.condition_assoc]
  refine RespectsLeft.precomp (Q := K.morphismProperty) _ ?_ _ (h _ _ ⟨i⟩)
  obtain ⟨j⟩ := hg
  exact (F.pullback₂ (E.f i)).morphismProperty j }
  | of_presieve f R hR h ih => {
  rw [K.mem_iff_exists_zeroHypercover] at hR
  obtain ⟨E,rfl⟩ := hR
  choose S hS h' using fun i : E.I₀ ↦ ih _ _ ⟨i⟩
  simp_rw [K.mem_iff_exists_zeroHypercover] at hS
  choose F hF using hS
  refine ⟨_, (E.bind F).mem₀, fun U g ⟨j⟩ ↦ ?_⟩
  dsimp
  rw [Category.assoc]
  exact h' _ _ _ (by simp [hF]) }
