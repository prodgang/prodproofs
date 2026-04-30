/-
Copyright (c) 2024 Edwin Agnew. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Edwin Agnew
-/
import ProdNum.QuotDefs
import ProdNum.PruneBasic
import ProdNum.GraftBasic
import ProdNum.Poset
import Mathlib.Order.Lattice

/-!
# Productive Numbers — Lattice Structure

Proves that `ProdNum` is a distributive lattice under graft (`⊔`) and prune (`⊓`).

## Main results

- `PreProdNum.distrib`: `x ⊓ (y ⊔ z) = (x ⊓ y) ⊔ (x ⊓ z)` (PreProdNum level)
- `PreProdNum.absorption1`, `absorption2`: absorption laws
- `instance : Lattice ProdNum`
- `instance : DistribLattice ProdNum`
-/

namespace PreProdNum

theorem distrib : ∀ x y z : PreProdNum, x ⊓ (y ⊔ z) = (x ⊓ y) ⊔ (x ⊓ z) := by
  apply PreProdNum.induction_list₃
  case h_zero_left => simp only [zero_prune, graft_zero, implies_true]
  case h_zero_mid => simp only [zero_graft, prune_zero, implies_true]
  case h_zero_right => simp only [graft_zero, prune_zero, implies_true]
  case h_nil_left => simp only [ne_eq, brak_graft_brak_ne_zero, not_false_eq_true, nil_prune_nz_eq_nil, brak_ne_zero, graft_nil_eq_self, implies_true]
  case h_nil_mid => simp only [ne_eq, brak_ne_zero, not_false_eq_true, nil_graft_eq_self, prune_nil_eq_nil, brak_prune_brak_ne_zero, implies_true]
  case h_nil_right => simp only [ne_eq, brak_ne_zero, not_false_eq_true, graft_nil_eq_self, prune_nil_eq_nil, brak_prune_brak_ne_zero, implies_true]
  case h_cons_cons_cons =>
    intros _ _ _ _ _ _ hx hxs
    simp only [prune, graft, brak.injEq, graft_list, prune_list, List.cons.injEq] at hxs ⊢
    exact ⟨hx, hxs⟩


theorem absorption1 : ∀ x y : PreProdNum, x ⊔ (x ⊓ y) = x := by
  apply PreProdNum.induction_list₂
  case h_zero_left => simp only [zero_prune, graft_zero, implies_true]
  case h_zero_right => simp only [prune_zero, graft_zero, implies_true]
  case h_nil_left => simp only [ne_eq, brak_ne_zero, not_false_eq_true, nil_prune_nz_eq_nil, graft_nil_eq_self, implies_true]
  case h_nil_right => simp only [ne_eq, brak_ne_zero, not_false_eq_true, prune_nil_eq_nil, graft_nil_eq_self, implies_true]
  case h_cons_cons =>
    intro x y xs ys hx hxs
    simp only [graft, prune, brak.injEq, prune_list, graft_list, List.cons.injEq] at hxs ⊢
    exact ⟨hx, hxs⟩

theorem absorption2 : ∀ x y : PreProdNum, x ⊓ (x ⊔ y) = x := by
  apply PreProdNum.induction_list₂
  case h_zero_left => simp only [zero_graft, zero_prune, implies_true]
  case h_zero_right =>  intro x; simp only [graft_zero, prune_idem]
  case h_nil_left => simp only [ne_eq, brak_ne_zero, not_false_eq_true, nil_graft_eq_self, nil_prune_nz_eq_nil, implies_true]
  case h_nil_right =>  simp only [ne_eq, brak_ne_zero, not_false_eq_true, graft_nil_eq_self, prune_idem, implies_true]
  case h_cons_cons =>
    intro x y xs ys hx hxs
    simp only [prune, graft, brak.injEq, graft_list, prune_list, List.cons.injEq] at hxs ⊢
    exact ⟨hx, hxs⟩

end PreProdNum

namespace ProdNum

theorem distrib (x y z : ProdNum) : x ⊓ (y ⊔ z) = (x ⊓ y) ⊔ (x ⊓ z) := by
  apply (lift_eq₃ PreProdNum.distrib) x y z


theorem absorption1 (x y : ProdNum) : x ⊔ (x ⊓ y) = x := by
  apply (lift_eq₂ PreProdNum.absorption1) x y


theorem absorption2 (x y : ProdNum) : x ⊓ (x ⊔ y) = x := by
  apply (lift_eq₂ PreProdNum.absorption2) x y


instance : Max ProdNum := ⟨graft⟩
instance : Min ProdNum := ⟨prune⟩

instance : Lattice ProdNum := Lattice.mk'
  (sup_comm  := graft_comm)
  (sup_assoc := graft_assoc)
  (inf_comm  := prune_comm)
  (inf_assoc := prune_assoc)
  (sup_inf_self := absorption1)
  (inf_sup_self := absorption2)

instance : DistribLattice ProdNum := DistribLattice.ofInfSupLe
  fun x y z => le_of_eq (distrib x y z)


lemma pleq_iff_le {x y : ProdNum} : x ⊑ y ↔ x ≤ y :=
  pleq_prune_iff.trans inf_eq_left

lemma zero_le (y : ProdNum) : ProdNum.zero ≤ y :=
  pleq_iff_le.mp (Quotient.ind (fun _ => mk_pleq_mk_iff.mpr PreProdNum.zero_pleq) y)

lemma le_of_mk_pleq {a b : PreProdNum} (h : PreProdNum.pleq a b) : (mk a : ProdNum) ≤ mk b :=
  pleq_iff_le.mp (mk_pleq_mk_iff.mpr h)

/-- Any `ProdNum` above `nil` has representative `brak xs` for some `xs`. -/
lemma exists_brak_rep_of_nil_le {x : ProdNum} (h : (nil : ProdNum) ≤ x) :
    ∃ xs, x.rep = PreProdNum.brak xs := by
  rcases hrep : x.rep with _ | xs
  · rw [← pleq_iff_le, ← mk_rep_eq (q := x), hrep, mk_pleq_mk_iff] at h
    exact absurd h (by simp only [PreProdNum.pleq, not_false_eq_true])
  · exact ⟨xs, rfl⟩

end ProdNum
