/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     AlgebraicGeometry.QuasicoherentTilde.aux_basicOpen_of_aux_restrict
Source:      Mathlib @ d0a050ad6, Mathlib/AlgebraicGeometry/Modules/Tilde.lean, line 798
             (added after the model's training data; human proof 26 tactic steps)
Experiment:  P1-astra-long-proofs, arm WT, solved after 4 call(s)
Prover:      gpt-6-astra
Setup:       GPT-6 Astra (Codex, effort medium), at most 10 calls per theorem: W = whole proof plus repair rounds;
             WT = W with read-only Mathlib sources to search; P = Lean-checked skeleton of have-steps, then one step per call
Check:       the proof replaced the human proof in the Mathlib file above; Lean reported
             0 errors and no `sorry`.
-/

private lemma aux_basicOpen_of_aux_restrict (M : (Spec R).Modules) (g : R)
    (h : Aux (M.restrict <|
        Spec.map <| CommRingCat.ofHom <| algebraMap R <| Localization.Away g) ⊤) :
      Aux M (basicOpen g) := by
  let ψ : R ⟶ CommRingCat.of (Localization.Away g) := CommRingCat.ofHom (algebraMap R (Localization.Away g))
  let φ := Spec.map ψ
  have hrange : φ.opensRange = basicOpen g := Scheme.Hom.opensRange_localizationAway g
  have htop : φ ''ᵁ ⊤ = basicOpen g := φ.image_top_eq_opensRange.trans hrange
  have himg (f : R) (hf : basicOpen f ≤ basicOpen g) : φ ''ᵁ basicOpen (ψ f) = basicOpen f := by { rw [← SpecMap_preimage_basicOpen, φ.image_preimage_eq_opensRange_inf, hrange, inf_eq_right.mpr hf] }
  let P (f : R) (V U : (Spec R).Opens) (hle : U ≤ V) : Prop := ∀ s : Γ(M, U), ∃ (n : ℕ) (t : Γ(M, V)), M.presheaf.map (homOfLE hle).op t = f ^ n • s
  let Q (f : R) (V U : (Spec R).Opens) (hle : U ≤ V) : Prop := ∀ t : Γ(M, V), M.presheaf.map (homOfLE hle).op t = 0 → ∃ n : ℕ, f ^ n • t = 0
  refine ⟨?_, ?_⟩
  · { intro f hf; change P f (basicOpen g) (basicOpen f) hf; have H : P f (φ ''ᵁ ⊤) (φ ''ᵁ basicOpen (ψ f)) (φ.image_mono le_top) := by { intro s; obtain ⟨n, t, ht⟩ := h.existence (ψ f) le_top s; refine ⟨n, t, ?_⟩; rw [← map_pow] at ht; exact ht.trans (M.restrictAppIso_smul_Spec ψ (f ^ n) s) }; simpa only [htop, himg f hf] using H }
  · { intro f hf; change Q f (basicOpen g) (basicOpen f) hf; have H : Q f (φ ''ᵁ ⊤) (φ ''ᵁ basicOpen (ψ f)) (φ.image_mono le_top) := by { intro t ht; obtain ⟨n, hn⟩ := h.uniqueness (ψ f) le_top t ht; refine ⟨n, ?_⟩; rw [← map_pow] at hn; exact (M.restrictAppIso_smul_Spec ψ (f ^ n) t).symm.trans hn }; simpa only [htop, himg f hf] using H }
