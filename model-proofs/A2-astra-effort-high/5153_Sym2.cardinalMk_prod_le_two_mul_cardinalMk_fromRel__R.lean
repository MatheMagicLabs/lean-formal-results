/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     Sym2.cardinalMk_prod_le_two_mul_cardinalMk_fromRel
Source:      Mathlib @ a02a63c2, Mathlib/Data/Sym/Sym2/Card.lean, line 119
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  A2-astra-effort-high, arm R, verified in round 0 (round 0 = first attempt)
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

theorem cardinalMk_prod_le_two_mul_cardinalMk_fromRel :
    #{ p : α × α // r p.fst p.snd } ≤ 2 * #(fromRel sym) := by
  classical
  let S := {p : α × α // r p.1 p.2}
  let f : S → fromRel sym :=
    fun p => ⟨s(p.1.1, p.1.2), by simpa using p.2⟩
  let c : Set.range f → S := fun y => Classical.choose y.2
  have hc (y : Set.range f) : f (c y) = y.1 :=
    Classical.choose_spec y.2
  let g : S → Bool × fromRel sym :=
    fun p => (decide (p = c ⟨f p, ⟨p, rfl⟩⟩), f p)
  have hg : Function.Injective g := by
    intro p q h
    have hf : f p = f q := congrArg Prod.snd h
    have hb :
        decide (p = c ⟨f p, ⟨p, rfl⟩⟩) =
          decide (q = c ⟨f q, ⟨q, rfl⟩⟩) :=
      congrArg Prod.fst h
    have hr :
        (⟨f p, ⟨p, rfl⟩⟩ : Set.range f) =
          ⟨f q, ⟨q, rfl⟩⟩ :=
      Subtype.ext hf
    rw [← hr] at hb
    let t := c ⟨f p, ⟨p, rfl⟩⟩
    change decide (p = t) = decide (q = t) at hb
    by_cases hp : p = t
    · have hq : q = t := by simpa [hp] using hb
      exact hp.trans hq.symm
    · have hq : q ≠ t := by simpa [hp] using hb
      have ht : f t = f p := hc ⟨f p, ⟨p, rfl⟩⟩
      have hpt := congrArg Subtype.val ht.symm
      have hqt := congrArg Subtype.val (hf.symm.trans ht.symm)
      change s(p.1.1, p.1.2) = s(t.1.1, t.1.2) at hpt
      change s(q.1.1, q.1.2) = s(t.1.1, t.1.2) at hqt
      have hpv : p.1 = t.1 ∨ p.1 = (t.1.2, t.1.1) := by
        simpa [Sym2.eq_iff, Prod.ext_iff] using hpt
      have hqv : q.1 = t.1 ∨ q.1 = (t.1.2, t.1.1) := by
        simpa [Sym2.eq_iff, Prod.ext_iff] using hqt
      rcases hpv with hpv | hpv
      · exact (hp (Subtype.ext hpv)).elim
      rcases hqv with hqv | hqv
      · exact (hq (Subtype.ext hqv)).elim
      exact Subtype.ext (hpv.trans hqv.symm)
  calc
    #S ≤ #(Bool × fromRel sym) := Cardinal.mk_le_of_injective hg
    _ = 2 * #(fromRel sym) := by simp [Cardinal.mk_prod]
