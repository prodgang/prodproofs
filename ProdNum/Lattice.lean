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

Proves that `QProd` is a distributive lattice under graft (`⊔`) and prune (`⊓`).

## Main results

- `RawProd.distrib`: `x ⊓ (y ⊔ z) = (x ⊓ y) ⊔ (x ⊓ z)` (raw level)
- `RawProd.absorption1`, `absorption2`: absorption laws
- `instance : Lattice QProd`
- `instance : DistribLattice QProd`
-/

namespace RawProd

theorem distrib : ∀ x y z : RawProd, x ⊓ (y ⊔ z) = (x ⊓ y) ⊔ (x ⊓ z) := by
  apply RawProd.induction_list₃
  case h_zero_left => simp only [zero_prune, graft_zero, implies_true]
  case h_zero_mid => simp only [zero_graft, prune_zero, implies_true]
  case h_zero_right => simp only [graft_zero, prune_zero, implies_true]
  case h_nil_left => simp only [ne_eq, brak_graft_brak_ne_zero, not_false_eq_true, nil_prune_nz_eq_nil, brak_ne_zero, graft_nil_eq_self, implies_true]
  case h_nil_mid => simp only [ne_eq, brak_ne_zero, not_false_eq_true, nil_graft_eq_self, prune_nil_eq_nil, brak_prune_brak_ne_zero, implies_true]
  case h_nil_right => simp only [ne_eq, brak_ne_zero, not_false_eq_true, graft_nil_eq_self, prune_nil_eq_nil, brak_prune_brak_ne_zero, implies_true]
  case h_cons_cons_cons =>
    intros _ _ _ _ _ _ hx hxs
    simp only [prune_raw, graft_raw, brak.injEq, graft_list, prune_list, List.cons.injEq] at hxs ⊢
    exact ⟨hx, hxs⟩


theorem absorption1 : ∀ x y : RawProd, x ⊔ (x ⊓ y) = x := by
  apply RawProd.induction_list₂
  case h_zero_left => simp only [zero_prune, graft_zero, implies_true]
  case h_zero_right => simp only [prune_zero, graft_zero, implies_true]
  case h_nil_left => simp only [ne_eq, brak_ne_zero, not_false_eq_true, nil_prune_nz_eq_nil, graft_nil_eq_self, implies_true]
  case h_nil_right => simp only [ne_eq, brak_ne_zero, not_false_eq_true, prune_nil_eq_nil, graft_nil_eq_self, implies_true]
  case h_cons_cons =>
    intro x y xs ys hx hxs
    simp only [graft_raw, prune_raw, brak.injEq, prune_list, graft_list, List.cons.injEq] at hxs ⊢
    exact ⟨hx, hxs⟩

theorem absorption2 : ∀ x y : RawProd, x ⊓ (x ⊔ y) = x := by
  apply RawProd.induction_list₂
  case h_zero_left => simp only [zero_graft, zero_prune, implies_true]
  case h_zero_right =>  intro x; simp only [graft_zero, prune_raw_idem]
  case h_nil_left => simp only [ne_eq, brak_ne_zero, not_false_eq_true, nil_graft_eq_self, nil_prune_nz_eq_nil, implies_true]
  case h_nil_right =>  simp only [ne_eq, brak_ne_zero, not_false_eq_true, graft_nil_eq_self, prune_raw_idem, implies_true]
  case h_cons_cons =>
    intro x y xs ys hx hxs
    simp only [prune_raw, graft_raw, brak.injEq, graft_list, prune_list, List.cons.injEq] at hxs ⊢
    exact ⟨hx, hxs⟩

end RawProd

namespace QProd

theorem distrib (x y z : QProd) : x ⊓ (y ⊔ z) = (x ⊓ y) ⊔ (x ⊓ z) := by
  apply (lift_eq₃ RawProd.distrib) x y z


theorem absorption1 (x y : QProd) : x ⊔ (x ⊓ y) = x := by
  apply (lift_eq₂ RawProd.absorption1) x y


theorem absorption2 (x y : QProd) : x ⊓ (x ⊔ y) = x := by
  apply (lift_eq₂ RawProd.absorption2) x y


instance : Max QProd := ⟨graft⟩
instance : Min QProd := ⟨prune⟩

instance : Lattice QProd := Lattice.mk'
  (sup_comm  := graft_comm)
  (sup_assoc := graft_assoc)
  (inf_comm  := prune_comm)
  (inf_assoc := prune_assoc)
  (sup_inf_self := absorption1)
  (inf_sup_self := absorption2)

instance : DistribLattice QProd := DistribLattice.ofInfSupLe
  fun x y z => le_of_eq (distrib x y z)


lemma pleq_iff_le {x y : QProd} : x ⊑ y ↔ x ≤ y :=
  pleq_prune_iff.trans inf_eq_left

lemma zero_le (y : QProd) : QProd.zero ≤ y :=
  pleq_iff_le.mp (Quotient.ind (fun _ => mk_pleq_mk_iff.mpr RawProd.zero_pleq) y)

lemma le_of_mk_pleq {a b : RawProd} (h : RawProd.pleq_raw a b) : (mk a : QProd) ≤ mk b :=
  pleq_iff_le.mp (mk_pleq_mk_iff.mpr h)

/-- Any `QProd` above `nil` has representative `brak xs` for some `xs`. -/
lemma exists_brak_rep_of_nil_le {x : QProd} (h : (nil : QProd) ≤ x) :
    ∃ xs, x.rep = RawProd.brak xs := by
  rcases hrep : x.rep with _ | xs
  · rw [← pleq_iff_le, ← mk_rep_eq (q := x), hrep, mk_pleq_mk_iff] at h
    exact absurd h (by simp only [RawProd.pleq_raw, not_false_eq_true])
  · exact ⟨xs, rfl⟩

end QProd
