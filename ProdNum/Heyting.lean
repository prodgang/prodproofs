/-
Copyright (c) 2024 Edwin Agnew. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Edwin Agnew
-/
import ProdNum.Poset
import ProdNum.Lattice
import Mathlib.Order.Sublattice
import Mathlib.Order.Heyting.Basic

/-!
# Productive Numbers — Heyting Algebra on Principal Downsets

For any `x : ProdNum`, the principal downset `Downset x = {y : ProdNum | y ≤ x}` carries
a Heyting algebra structure.

## Main definitions

- `PreProdNum.himp`, `PreProdNum.himp_list`: Heyting implication relative to a bound
- `ProdNum.Downset`: the principal downset type `{y | y ≤ x}`
- `ProdNum.himp_Downset`: Heyting implication on `Downset x`

## Main results

- `himp_pleq_bound`: `himp x a b ⊑ x`
- `himp_adjunction`: `a ⊑ x → (a ⊑ himp x b c ↔ a ⊓ b ⊑ c)`
- `instance (x : ProdNum) : HeytingAlgebra (Downset x)`
-/

namespace PreProdNum

mutual
  /-- Heyting implication relative to bound `x`:
      `himp x a b` is the greatest `c ⊑ x` such that `a ⊓ c ⊑ b`. -/
  def himp : PreProdNum → PreProdNum → PreProdNum → PreProdNum
    | zero,    _,       _       => zero
    | x,       zero,    _       => x
    | _,       _,       zero    => zero
    | brak xs, brak as, brak bs => brak (himp_list xs as bs)

  /-- Componentwise himp on lists: recurse on the bound list,
      reading head elements of `as` and `bs` via `get`. -/
  def himp_list : List PreProdNum → List PreProdNum → List PreProdNum → List PreProdNum
    | [],       _,  _  => []
    | x :: xs,  as, bs =>
        himp x (get as 0) (get bs 0) :: himp_list xs as.tail bs.tail
end

private lemma get_tail (xs : List PreProdNum) (i : ℕ) : get xs (i + 1) = get xs.tail i := by
  cases xs with
  | nil => simp only [get_nil, List.tail_nil]
  | cons _ _ => simp only [get_cons_succ, List.tail_cons]


/-- `himp x a b ⊑ x`: the result is always bounded by `x`. -/
lemma himp_pleq_bound (x a b : PreProdNum) : himp x a b ⊑ x := by
  revert x a b
  apply induction
  case h_zero => intro a b; simp only [himp, pleq_refl]
  case h_brak =>
    intro xs hx a b
    cases a
    · simp only [himp, pleq_refl]
    · rename_i as
      cases b
      · simp only [himp, zero_pleq]
      · rename_i bs
        simp only [himp]
        induction xs generalizing as bs with
        | nil => simp only [himp_list, nil_pleq_brak]
        | cons xh xt ih =>
          simp only [pleq, himp_list, pleq_list] at ih ⊢
          exact ⟨hx xh (List.mem_cons.mpr (.inl rfl)) _ _,
                 ih (fun x hxt a b => hx x (List.mem_cons_of_mem xh hxt) a b) as.tail bs.tail⟩


/-- Core Heyting adjunction: `a ⊑ x → (a ⊑ himp x b c ↔ a ⊓ b ⊑ c)`. -/
lemma himp_adjunction {x a b c : PreProdNum} (ha : a ⊑ x) :
    a ⊑ himp x b c ↔ a ⊓ b ⊑ c := by
  -- Generalise over a b c before induction so the IH is ∀ a b c, not specialised.
  suffices key : ∀ y a b c : PreProdNum, a ⊑ y → (a ⊑ himp y b c ↔ a ⊓ b ⊑ c) from key x a b c ha
  intro y
  induction y using PreProdNum.induction_list
  case h_zero =>
    intro a b c ha
    rw [pleq_zero_eq_zero ha]
    simp only [himp, zero_pleq, zero_prune]
  case h_nil =>
    intro a b c ha
    cases a <;> cases b <;> cases c
    all_goals simp only [himp, zero_pleq, prune_zero, zero_prune,
      iff_true]
    · exact ha
    · exact ha
    · rename_i as bs
      constructor
      · intro h; simp only [pleq] at h
      · intro h; exact absurd (pleq_zero_eq_zero h) (brak_prune_brak_ne_zero _ _)
    · rename_i as bs cs
      constructor
      · intro _
        have haz := brak_pleq_nil_iff_allzero.mp ha
        suffices h : brak as ⊓ brak bs ⊑ brak [] from pleq_transitivity h nil_pleq_brak
        rw [allzero_prune_eq_replicate haz]
        exact replicate_zero_pleq_brak _
      · intro _; exact ha
  case h_cons xh xs ih_head ih_tail =>
    intro a b c ha
    cases a with
    | zero => simp only [himp, zero_pleq, zero_prune]
    | brak as =>
      cases b with
      | zero => simp only [himp, prune_zero, zero_pleq, iff_true]; exact ha
      | brak bs =>
        cases c with
        | zero =>
          simp only [himp]
          constructor
          · intro h; simp only [pleq] at h
          · intro h; exact absurd (pleq_zero_eq_zero h) (brak_prune_brak_ne_zero _ _)
        | brak cs =>
          simp only [himp, himp_list]
          cases as with
          | nil =>
            simp only [nil_pleq_brak, ne_eq, brak_ne_zero, not_false_eq_true, nil_prune_nz_eq_nil]
          | cons ah at_ =>
            obtain ⟨ha_head, ha_tail⟩ := cons_pleq_cons_iff.mp ha
            have iff_head := ih_head ah (get bs 0) (get cs 0) ha_head
            have iff_tail := ih_tail (brak at_) (brak bs.tail) (brak cs.tail) ha_tail
            cases bs with
            | nil =>
              constructor
              . intro h
                exact nil_pleq_brak
              . intro _
                apply cons_pleq_cons_iff.mpr
                simp only [get_nil, prune_zero, zero_pleq, iff_true] at iff_head
                simp only [List.tail_nil, ne_eq, brak_ne_zero, not_false_eq_true, prune_nil_nz_eq_nil, nil_pleq_brak, iff_true] at iff_tail
                exact ⟨iff_head, iff_tail⟩
            | cons bh bt =>
              cases cs with
              | nil =>
                rw [cons_prune_cons]
                constructor
                · intro h
                  obtain ⟨hh, ht⟩ := cons_pleq_cons_iff.mp h
                  rw [brak_pleq_nil_iff_allzero, allzero, List.length_cons,
                      List.replicate_succ, List.cons.injEq]
                  exact ⟨pleq_zero_eq_zero (iff_head.mp hh), brak_pleq_nil_iff_allzero.mp (iff_tail.mp ht)⟩
                · intro h
                  rw [brak_pleq_nil_iff_allzero, allzero, List.length_cons,
                      List.replicate_succ, List.cons.injEq] at h
                  obtain ⟨hh, ht⟩ := h
                  exact cons_pleq_cons_iff.mpr ⟨iff_head.mpr (hh ▸ zero_pleq),
                                                 iff_tail.mpr (brak_pleq_nil_iff_allzero.mpr ht)⟩
              | cons ch ct =>
                simp only [get_cons_zero, List.tail_cons]
                rw [cons_prune_cons]
                constructor
                · intro h
                  obtain ⟨hh, ht⟩ := cons_pleq_cons_iff.mp h
                  exact cons_pleq_cons_iff.mpr ⟨iff_head.mp hh, iff_tail.mp ht⟩
                · intro h
                  obtain ⟨hh, ht⟩ := cons_pleq_cons_iff.mp h
                  exact cons_pleq_cons_iff.mpr ⟨iff_head.mpr hh, iff_tail.mpr ht⟩

end PreProdNum

namespace ProdNum

open PreProdNum

@[reducible]
def downsetSublattice (x : ProdNum) : Sublattice ProdNum where
  carrier    := {y | y ≤ x}
  supClosed' := fun _ ha _ hb => Set.mem_setOf.mpr (sup_le ha hb)
  infClosed' := fun _ ha _ _ => Set.mem_setOf.mpr (inf_le_left.trans ha)


lemma pleq_iff_downset {x y : ProdNum} : x ≤ y ↔ x ∈ y.downsetSublattice := by
  simp only [Sublattice.mem_mk, Set.mem_setOf_eq]


/-- The principal downset `{y : ProdNum | y ≤ x}` as a type. -/
abbrev Downset (x : ProdNum) : Type := ↥(downsetSublattice x)

instance (x : ProdNum) : Lattice (Downset x) := inferInstance

instance (x : ProdNum) : DistribLattice (Downset x) :=
  DistribLattice.ofInfSupLe fun a b c => by
    apply le_of_eq; apply Subtype.ext
    exact ProdNum.distrib a.val b.val c.val

instance (x : ProdNum) : BoundedOrder (Downset x) where
  top    := ⟨x, pleq_iff_downset.mp (le_refl x)⟩
  le_top := fun a => a.2
  bot    := ⟨ProdNum.zero, pleq_iff_downset.mp (zero_le x)⟩
  bot_le := fun a => zero_le a.val



lemma le_mk_iff {v : ProdNum} {y : PreProdNum} : v ≤ mk y ↔ (rep v) ⊑ y := by
  rw [← pleq_iff_le]
  conv_lhs => rw [← mk_rep_eq (q := v)]
  exact mk_pleq_mk_iff

/-- `a ⊓ b ≤ c ↔ pleq (rep a ⊓ rep b) (rep c)`:
    lifts PreProdNum-level `⊓` to the ProdNum order. -/
lemma inf_le_iff_pleq {a b c : ProdNum} : prune a b ≤ c ↔ (rep a ⊓ rep b) ⊑ (rep c) := by
  conv_lhs => rw [← mk_rep_eq (q := a), ← mk_rep_eq (q := b), prune_mk_mk, ← mk_rep_eq (q := c)]
  exact pleq_iff_le.symm.trans mk_pleq_mk_iff

/-- Restricts `himp` to the subtype `Downset x`-/
def himp_Downset (x : ProdNum) (a b : Downset x) : Downset x :=
  ⟨mk (PreProdNum.himp (rep x) (rep a.1) (rep b.1)),
   pleq_iff_downset.mp (pleq_iff_le.mp (by
     have h := mk_pleq_mk_iff.mpr (PreProdNum.himp_pleq_bound (rep x) (rep a.1) (rep b.1))
     rwa [mk_rep_eq] at h))⟩

instance (x : ProdNum) : HeytingAlgebra (Downset x) :=
  HeytingAlgebra.ofHImp (himp_Downset x) fun a _ _ =>
    le_mk_iff.trans ((PreProdNum.himp_adjunction (pleq_iff_le.mpr a.2)).trans inf_le_iff_pleq.symm)

end ProdNum
