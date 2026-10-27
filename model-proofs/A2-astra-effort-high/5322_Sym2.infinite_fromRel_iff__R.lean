/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     Sym2.infinite_fromRel_iff
Source:      Mathlib @ a02a63c2, Mathlib/Data/Sym/Sym2/Card.lean, line 150
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  A2-astra-effort-high, arm R, verified in round 3 (round 0 = first attempt)
Prover:      gpt-6-astra
Setup:       GPT-6 Astra, reasoning effort high (arms R, N0)
Check:       the proof replaced the human proof in the Mathlib file above; Lean reported
             0 errors and no `sorry`; sorry/admit/native_decide/search tactics were rejected.
-/

namespace Sym2
open scoped Cardinal
variable {α : Type*}
variable (α) in
open scoped Classical in
variable (α) in
variable (α) in
variable (α) in
open scoped Classical in
variable (α) in
variable (α) in
section fromRel
variable {r : α → α → Prop} (sym : Std.Symm r)

theorem infinite_fromRel_iff : (fromRel sym).Infinite ↔ { p : α × α | r p.fst p.snd }.Infinite := by
  classical
  have hf (z : Sym2 α) :
      {p : α × α | s(p.1, p.2) = z}.Finite := by
    refine Sym2.inductionOn z ?_
    intro a b
    have he :
        {p : α × α | s(p.1, p.2) = s(a, b)} =
          {(a, b), (b, a)} := by
      ext p
      simp [Sym2.eq_iff, Prod.ext_iff]
    rw [he]
    simp
  have he :
      fromRel sym =
        (fun p : α × α => s(p.1, p.2)) ''
          {p : α × α | r p.1 p.2} := by
    ext z
    constructor
    · refine Sym2.inductionOn z ?_
      intro a b hz
      exact ⟨(a, b), hz, rfl⟩
    · rintro ⟨p, hp, rfl⟩
      exact hp
  change (¬ (fromRel sym).Finite) ↔
    (¬ {p : α × α | r p.1 p.2}.Finite)
  apply not_congr
  constructor
  · intro hs
    letI : Finite (fromRel sym) := hs
    letI : Fintype (fromRel sym) := Fintype.ofFinite _
    letI : ∀ z : fromRel sym,
        Finite {p : α × α // s(p.1, p.2) = z.1} :=
      fun z => hf z.1
    letI : ∀ z : fromRel sym,
        Fintype {p : α × α // s(p.1, p.2) = z.1} :=
      fun z => Fintype.ofFinite _
    let f : {p : α × α // r p.1 p.2} →
        Σ z : fromRel sym, {p : α × α // s(p.1, p.2) = z.1} :=
      fun p => ⟨⟨s(p.1.1, p.1.2), p.2⟩, ⟨p.1, rfl⟩⟩
    exact Finite.of_injective f (by
      intro p q h
      apply Subtype.ext
      exact congrArg
        (fun x : Σ z : fromRel sym,
          {p : α × α // s(p.1, p.2) = z.1} => x.2.1) h)
  · intro hs
    rw [he]
    exact hs.image _
