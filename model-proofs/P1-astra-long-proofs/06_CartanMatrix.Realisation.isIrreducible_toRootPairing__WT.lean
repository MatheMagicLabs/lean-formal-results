/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     CartanMatrix.Realisation.isIrreducible_toRootPairing
Source:      Mathlib @ d0a050ad6, Mathlib/LinearAlgebra/Matrix/Cartan/Realisation.lean, line 526
             (added after the model's training data; human proof 36 tactic steps)
Experiment:  P1-astra-long-proofs, arm WT, solved after 1 call(s)
Prover:      gpt-6-astra
Setup:       GPT-6 Astra (Codex, effort medium), at most 10 calls per theorem: W = whole proof plus repair rounds;
             WT = W with read-only Mathlib sources to search; P = Lean-checked skeleton of have-steps, then one step per call
Check:       the proof replaced the human proof in the Mathlib file above; Lean reported
             0 errors and no `sorry`.
-/

lemma isIrreducible_toRootPairing [Nonempty n] {k V W : Type*} [Field k] [CharZero k]
    [AddCommGroup V] [Module k V] [AddCommGroup W] [Module k W] (rl : Realisation n k V W)
    (hr : span k (range rl.sRoot) = ⊤)
    (hA' : rl.matrix.IsIndecomposable) :
    rl.toRootPairing.IsIrreducible := by
  classical
  haveI : Nontrivial V :=
    ⟨⟨rl.sRoot (Classical.arbitrary n), 0,
      rl.lin_ind_sRoot.ne_zero (Classical.arbitrary n)⟩⟩
  apply RootPairing.IsIrreducible.mk'
  intro q hq hq0
  have hker (j : n) (hj : rl.sRoot j ∉ q) (x : V) (hx : x ∈ q) :
      rl.pairing x (rl.sCoroot j) = 0 := by
    have hs := hq ⟨_, rl.sPair_mem_idx j⟩ hx
    change x - rl.pairing x (rl.sCoroot j) • rl.sRoot j ∈ q at hs
    have ht : rl.pairing x (rl.sCoroot j) • rl.sRoot j ∈ q := by
      simpa using q.sub_mem hx hs
    by_contra hn
    exact hj ((q.smul_mem_iff hn).mp ht)
  have hex : ∃ i, rl.sRoot i ∈ q := by
    by_contra hn
    push_neg at hn
    obtain ⟨x, hx, hx0⟩ := q.ne_bot_iff.mp hq0
    apply hx0
    apply (rl.flip.eq_iff_forall_pairing_sRoot_eq
      (y₁ := x) (y₂ := 0) (by simpa using (show x ∈ span k (range rl.sRoot) by
        rw [hr]
        exact Submodule.mem_top))).mpr
    intro i
    simpa using hker i (hn i) x hx
  let b : n → ℕ := fun i ↦ if rl.sRoot i ∈ q then 1 else 0
  have hb : rl.matrix.BlockTriangular b := by
    intro i j hij
    have hi : rl.sRoot i ∈ q := by
      by_contra hi
      simp [b, hi] at hij
    have hj : rl.sRoot j ∉ q := by
      intro hj
      simp [b, hi, hj] at hij
    have hz := hker j hj (rl.sRoot i) hi
    simpa using hz
  obtain ⟨a, ha⟩ :=
    (Matrix.isIndecomposable_iff_blockTriangular_const rl.matrix).mp hA' b hb
  obtain ⟨i, hi⟩ := hex
  have hall (j : n) : rl.sRoot j ∈ q := by
    have he : b j = b i := by rw [ha]; rfl
    by_contra hj
    simp [b, hi, hj] at he
  rw [eq_top_iff, ← hr]
  apply Submodule.span_le.mpr
  rintro _ ⟨j, rfl⟩
  exact hall j
