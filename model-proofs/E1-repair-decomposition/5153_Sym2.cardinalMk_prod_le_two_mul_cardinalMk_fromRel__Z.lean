/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     Sym2.cardinalMk_prod_le_two_mul_cardinalMk_fromRel
Source:      Mathlib @ a02a63c2, Mathlib/Data/Sym/Sym2/Card.lean, line 119
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  E1-repair-decomposition, arm Z, verified in round 1 (round 0 = first attempt)
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

theorem cardinalMk_prod_le_two_mul_cardinalMk_fromRel :
    #{ p : α × α // r p.fst p.snd } ≤ 2 * #(fromRel sym) := by
  classical
  have hrep : ∀ z : Sym2 α, ∃ p : α × α, s(p.1, p.2) = z := by
    intro z
    refine Sym2.inductionOn z ?_
    intro a b
    exact ⟨(a, b), rfl⟩
  let rep : Sym2 α → α × α := fun z => Classical.choose (hrep z)
  have rep_spec (z : Sym2 α) : s((rep z).1, (rep z).2) = z :=
    Classical.choose_spec (hrep z)
  let f : { p : α × α // r p.fst p.snd } → fromRel sym :=
    fun p => ⟨s(p.val.fst, p.val.snd), by simpa using p.property⟩
  let g : { p : α × α // r p.fst p.snd } → Bool × fromRel sym :=
    fun p => (decide (p.val = rep (f p).val), f p)
  have hg : Function.Injective g := by
    intro p q h
    have hf : f p = f q := congrArg Prod.snd h
    let t : α × α := rep (f p).val
    have ht : s(t.fst, t.snd) = (f p).val := rep_spec _
    have hp : p.val = t ∨ p.val = t.swap := by
      have he : s(p.val.fst, p.val.snd) = s(t.fst, t.snd) := ht.symm
      simpa [Sym2.eq_iff, Prod.ext_iff] using he
    have hq : q.val = t ∨ q.val = t.swap := by
      have he : s(q.val.fst, q.val.snd) = s(t.fst, t.snd) :=
        (congrArg Subtype.val hf).symm.trans ht.symm
      simpa [Sym2.eq_iff, Prod.ext_iff] using he
    have hb : decide (p.val = t) = decide (q.val = t) := by
      have hb := congrArg Prod.fst h
      change decide (p.val = rep (f p).val) =
        decide (q.val = rep (f q).val) at hb
      rw [← hf] at hb
      exact hb
    apply Subtype.ext
    rcases hp with hp | hp <;> rcases hq with hq | hq
    · exact hp.trans hq.symm
    · have hqt : q.val = t := by
        by_contra hn
        simp [hp, hn] at hb
      exact hp.trans hqt.symm
    · have hpt : p.val = t := by
        by_contra hn
        simp [hq, hn] at hb
      exact hpt.trans hq.symm
    · exact hp.trans hq.symm
  calc
    #{ p : α × α // r p.fst p.snd } ≤ #(Bool × fromRel sym) :=
      Cardinal.mk_le_of_injective hg
    _ = 2 * #(fromRel sym) := by simp
