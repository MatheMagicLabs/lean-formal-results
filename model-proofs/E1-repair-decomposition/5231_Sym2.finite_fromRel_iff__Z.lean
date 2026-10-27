/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     Sym2.finite_fromRel_iff
Source:      Mathlib @ a02a63c2, Mathlib/Data/Sym/Sym2/Card.lean, line 140
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  E1-repair-decomposition, arm Z, verified in round 2 (round 0 = first attempt)
Prover:      gpt-6-astra
Setup:       GPT-6 Astra, which part of Lean feedback makes repair work: after a shared first attempt (E0), V = full error messages, Z = line numbers only, B = only "Lean rejected this proof"
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

theorem finite_fromRel_iff : (fromRel sym).Finite ↔ Finite { p : α × α // r p.fst p.snd } := by
  classical
  have reps : ∀ q : Sym2 α, ∃ p : α × α, s(p.1, p.2) = q := by
    intro q
    first
    | exact Quotient.inductionOn q (fun p => ⟨p, rfl⟩)
    | exact Quot.inductionOn q (fun p => ⟨p, rfl⟩)
  let rep (q : Sym2 α) : α × α := Classical.choose (reps q)
  have rep_spec (q : Sym2 α) : s((rep q).1, (rep q).2) = q :=
    Classical.choose_spec (reps q)
  have alternatives (p t : α × α)
      (h : s(p.1, p.2) = s(t.1, t.2)) :
      p = t ∨ p = t.swap := by
    rcases p with ⟨a, b⟩
    rcases t with ⟨c, d⟩
    simpa [Sym2.eq_iff, Prod.ext_iff] using h
  let f : {p : α × α // r p.1 p.2} → ↥(fromRel sym) :=
    fun p => ⟨s(p.val.1, p.val.2), by simpa using p.property⟩
  constructor
  · intro h
    letI := h.fintype
    let g : {p : α × α // r p.1 p.2} → ↥(fromRel sym) × Bool :=
      fun p => (f p, decide (p.val = rep (f p).val))
    apply Finite.of_injective g
    intro p t hpt
    have hf : f p = f t := congrArg Prod.fst hpt
    have hb :
        decide (p.val = rep (f p).val) =
          decide (t.val = rep (f p).val) := by
      have hh := congrArg Prod.snd hpt
      simpa only [g, hf] using hh
    have hp :
        p.val = rep (f p).val ∨
          p.val = (rep (f p).val).swap :=
      alternatives _ _ (rep_spec (f p).val).symm
    have ht :
        t.val = rep (f p).val ∨
          t.val = (rep (f p).val).swap := by
      apply alternatives
      rw [rep_spec]
      exact (congrArg Subtype.val hf).symm
    apply Subtype.ext
    by_cases he : p.val = rep (f p).val
    · have he' : t.val = rep (f p).val := by
        simpa [he] using hb.symm
      exact he.trans he'.symm
    · have he' : t.val ≠ rep (f p).val := by
        simpa [he] using hb.symm
      exact (hp.resolve_left he).trans (ht.resolve_left he').symm
  · intro h
    letI := h
    have hs : Function.Surjective f := by
      intro q
      obtain ⟨p, hp⟩ := reps q.val
      have hr : r p.1 p.2 := by
        have hh := q.property
        rw [← hp] at hh
        simpa using hh
      exact ⟨⟨p, hr⟩, Subtype.ext hp⟩
    haveI : Finite ↥(fromRel sym) := Finite.of_surjective f hs
    exact Set.toFinite _
