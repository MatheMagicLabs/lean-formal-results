/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     SSet.prodStdSimplex.pairingCore.IsType₂.strictMono_φ
Source:      Mathlib @ d0a050ad6, Mathlib/AlgebraicTopology/SimplicialSet/AnodyneExtensions/UnionProd.lean, line 342
             (added after the model's training data; human proof 34 tactic steps)
Experiment:  P1-astra-long-proofs, arm W, solved after 4 call(s)
Prover:      gpt-6-astra
Setup:       GPT-6 Astra (Codex, effort medium), at most 10 calls per theorem: W = whole proof plus repair rounds;
             WT = W with read-only Mathlib sources to search; P = Lean-checked skeleton of have-steps, then one step per call
Check:       the proof replaced the human proof in the Mathlib file above; Lean reported
             0 errors and no `sorry`.
-/

lemma strictMono_φ : StrictMono (φ x hd) := by
  classical
  have hs : StrictMono (objEquiv (x.cast hd).simplex) := by
    first
    | exact (nonDegenerate_iff_strictMono_objEquiv _).1 (x.cast hd).nonDegenerate
    | exact (nonDegenerate_iff_strictMono_objEquiv).1 (x.cast hd).nonDegenerate
    | exact (mem_nonDegenerate_iff_strictMono_objEquiv _).1 (x.cast hd).nonDegenerate
    | exact (mem_nonDegenerate_iff_strictMono_objEquiv).1 (x.cast hd).nonDegenerate
    | exact objEquiv_strictMono (x.cast hd).nonDegenerate
    | exact strictMono_objEquiv_of_nonDegenerate (x.cast hd).nonDegenerate
    | exact (objEquiv_strictMono_iff _).2 (x.cast hd).nonDegenerate
    | exact (strictMono_iff _).2 (x.cast hd).nonDegenerate
    | apply (objEquiv (x.cast hd).simplex).monotone.strictMono_of_injective
      first
      | exact (nonDegenerate_iff_injective_objEquiv _).1 (x.cast hd).nonDegenerate
      | exact (nonDegenerate_iff_injective_objEquiv).1 (x.cast hd).nonDegenerate
      | exact (mem_nonDegenerate_iff_injective_objEquiv _).1 (x.cast hd).nonDegenerate
      | exact (mem_nonDegenerate_iff_injective_objEquiv).1 (x.cast hd).nonDegenerate
      | exact objEquiv_injective (x.cast hd).nonDegenerate
  let p := min x hd
  have hleft (i : Fin (d + 2)) (hi : i < p.castSucc) :
      φ x hd i < φ x hd p.castSucc := by
    have hi' : i.val < p.val := hi
    have hilast : i ≠ Fin.last (d + 1) := by
      intro h
      have hv := congrArg Fin.val h
      change i.val = d + 1 at hv
      have hp := p.isLt
      omega
    let a : Fin (d + 1) := i.castPred hilast
    have ha : a < p := hi'
    rw [φ_of_lt x hd i hi, φ_castSucc]
    change objEquiv (x.cast hd).simplex a <
      (k.castSucc, (x.cast hd).simplex.2 p)
    have hf : (x.cast hd).simplex.1 a ≤ k.castSucc :=
      (simplex_fst_le_castSucc_iff x hd a).2 ha
    have hg := stdSimplex.monotone_apply (x.cast hd).simplex.2 ha.le
    refine lt_iff_le_not_ge.mpr ⟨⟨hf, hg⟩, ?_⟩
    intro h
    have hp : p ≠ 0 := by
      intro hp
      rw [hp] at ha
      exact (not_lt_of_ge (Fin.zero_le a)) ha
    let l : Fin d := p.pred hp
    have hl : l.succ = p := by simp [l]
    have hal : a ≤ l.castSucc := by
      rw [← hl] at ha
      exact (Fin.le_castSucc_iff).2 ha
    have hlp : l.castSucc < min x hd := by
      change l.castSucc < p
      rw [← hl]
      exact Fin.castSucc_lt_succ
    have hf' : (x.cast hd).simplex.1 l.castSucc = k.castSucc :=
      le_antisymm
        ((simplex_fst_le_castSucc_iff x hd l.castSucc).2 hlp)
        (le_trans h.1
          (stdSimplex.monotone_apply (x.cast hd).simplex.1 hal))
    have hg' :
        (x.cast hd).simplex.2 l.succ =
          (x.cast hd).simplex.2 l.castSucc := by
      apply le_antisymm
      · rw [hl]
        exact le_trans h.2
          (stdSimplex.monotone_apply (x.cast hd).simplex.2 hal)
      · exact stdSimplex.monotone_apply _
          (show l.castSucc ≤ l.succ from Fin.castSucc_lt_succ.le)
    apply hx d hd l.succ
    rw [isIndex_succ]
    refine ⟨hf', ?_, hg'⟩
    rw [hl]
    exact simplex_fst_min x hd
  have hright (i : Fin (d + 2)) (hi : p.castSucc < i) :
      φ x hd p.castSucc < φ x hd i := by
    have hi' : p.val < i.val := hi
    have hi0 : i ≠ 0 := by
      intro h
      have hv := congrArg Fin.val h
      change i.val = 0 at hv
      omega
    have hpi : p ≤ i.pred hi0 := by
      change p.val ≤ i.val - 1
      omega
    rw [φ_castSucc, φ_of_gt x hd i hi]
    have hf : (x.cast hd).simplex.1 p ≤
        (x.cast hd).simplex.1 (i.pred hi0) :=
      stdSimplex.monotone_apply (x.cast hd).simplex.1 hpi
    have hg : (x.cast hd).simplex.2 p ≤
        (x.cast hd).simplex.2 (i.pred hi0) :=
      stdSimplex.monotone_apply (x.cast hd).simplex.2 hpi
    have hfp : (x.cast hd).simplex.1 p = k.succ :=
      simplex_fst_min x hd
    have hf' : k.succ ≤ (x.cast hd).simplex.1 (i.pred hi0) :=
      hfp ▸ hf
    have hk : k.castSucc < k.succ := Fin.castSucc_lt_succ
    refine lt_iff_le_not_ge.mpr ⟨⟨le_trans hk.le hf', hg⟩, ?_⟩
    intro h
    exact (not_le_of_gt hk) (le_trans hf' h.1)
  intro i j hij
  rcases lt_trichotomy i p.castSucc with hi | hi | hi
  · rcases lt_trichotomy j p.castSucc with hj | hj | hj
    · rw [φ_of_lt x hd i hi, φ_of_lt x hd j hj]
      apply hs
      exact hij
    · subst j
      exact hleft i hi
    · exact lt_trans (hleft i hi) (hright j hj)
  · subst i
    exact hright j hij
  · have hj : p.castSucc < j := lt_trans hi hij
    rw [φ_of_gt x hd i hi, φ_of_gt x hd j hj]
    apply hs
    change i.val - 1 < j.val - 1
    have hi' : p.val < i.val := hi
    have hij' : i.val < j.val := hij
    omega
