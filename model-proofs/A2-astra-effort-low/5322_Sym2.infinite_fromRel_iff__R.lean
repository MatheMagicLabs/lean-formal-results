/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     Sym2.infinite_fromRel_iff
Source:      Mathlib @ a02a63c2, Mathlib/Data/Sym/Sym2/Card.lean, line 150
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  A2-astra-effort-low, arm R, verified in round 1 (round 0 = first attempt)
Prover:      gpt-6-astra
Setup:       GPT-6 Astra, reasoning effort low (arms R, N0)
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
  let q : α × α → Sym2 α := fun p => s(p.1, p.2)
  have hmem (p : α × α) :
      q p ∈ fromRel sym ↔ r p.1 p.2 := by
    simp [q]
  have hrep (z : Sym2 α) : ∃ p : α × α, q p = z := by
    induction z using Sym2.ind with
    | _ a b => exact ⟨(a, b), rfl⟩
  choose rep hrep using hrep
  have himage : q '' {p : α × α | r p.1 p.2} = fromRel sym := by
    apply Set.Subset.antisymm
    · rintro _ ⟨p, hp, rfl⟩
      exact (hmem p).2 hp
    · intro z hz
      refine ⟨rep z, ?_, hrep z⟩
      apply (hmem (rep z)).1
      rwa [hrep z]
  have hfinite :
      (fromRel sym).Finite ↔ {p : α × α | r p.1 p.2}.Finite := by
    constructor
    · intro h
      have hf := (h.image rep).union
        (h.image (fun z => (rep z).swap))
      apply hf.subset
      intro p hp
      have hz : q p ∈ fromRel sym := (hmem p).2 hp
      have he : p = rep (q p) ∨ p = (rep (q p)).swap := by
        have he := (hrep (q p)).symm
        simpa [q, Prod.ext_iff] using he
      rcases he with he | he
      · exact Or.inl ⟨q p, hz, he.symm⟩
      · exact Or.inr ⟨q p, hz, he.symm⟩
    · intro h
      rw [← himage]
      exact h.image q
  exact not_congr hfinite
