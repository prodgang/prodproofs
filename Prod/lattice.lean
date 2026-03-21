import Prod.quot_defs
import Prod.prune_basic
import Prod.graft_basic
import Prod.poset
import Mathlib.Order.Lattice

namespace RawProd

theorem distrib : ∀ x y z : RawProd, x ⊓ (y ⊔ z) = (x ⊓ y) ⊔ (x ⊓ z) := by
  apply RawProd.induction_list₃
  case h_zero_left => simp only [zero_prune_eq_zero, graft_zero_eq_self, implies_true]
  case h_zero_mid => simp only [zero_graft_eq_self, prune_zero_eq_zero, implies_true]
  case h_zero_right => simp only [graft_zero_eq_self, prune_zero_eq_zero, implies_true]
  case h_nil_left => simp only [ne_eq, brak_graft_brak_neq_zero, not_false_eq_true, nil_prune_nz_eq_nil, brak_neq_zero, graft_nil_eq_self, implies_true]
  case h_nil_mid => simp only [ne_eq, brak_neq_zero, not_false_eq_true, nil_graft_eq_self, prune_nil_eq_nil, brak_prune_brak_neq_zero, implies_true]
  case h_nil_right => simp only [ne_eq, brak_neq_zero, not_false_eq_true, graft_nil_eq_self, prune_nil_eq_nil, brak_prune_brak_neq_zero, implies_true]
  case h_cons_cons_cons =>
    intros _ _ _ _ _ _ hx hxs
    simp only [prune_raw, graft_raw, brak.injEq, graft_list, prune_list, List.cons.injEq] at hxs ⊢
    exact ⟨hx, hxs⟩


theorem absorption1 : ∀ x y : RawProd, x ⊔ (x ⊓ y) = x := by
  apply RawProd.induction_list₂
  case h_zero_left => simp only [zero_prune_eq_zero, graft_zero_eq_self, implies_true]
  case h_zero_right => simp only [prune_zero_eq_zero, graft_zero_eq_self, implies_true]
  case h_nil_left => simp only [ne_eq, brak_neq_zero, not_false_eq_true, nil_prune_nz_eq_nil, graft_nil_eq_self, implies_true]
  case h_nil_right => simp only [ne_eq, brak_neq_zero, not_false_eq_true, prune_nil_eq_nil, graft_nil_eq_self, implies_true]
  case h_cons_cons =>
    intro x y xs ys hx hxs
    simp only [graft_raw, prune_raw, brak.injEq, prune_list, graft_list, List.cons.injEq] at hxs ⊢
    exact ⟨hx, hxs⟩

theorem absorption2 : ∀ x y : RawProd, x ⊓ (x ⊔ y) = x := by
  apply RawProd.induction_list₂
  case h_zero_left => simp only [zero_graft_eq_self, zero_prune_eq_zero, implies_true]
  case h_zero_right =>  intro x; simp only [graft_zero_eq_self, prune_raw_idem]
  case h_nil_left => simp only [ne_eq, brak_neq_zero, not_false_eq_true, nil_graft_eq_self, nil_prune_nz_eq_nil, implies_true]
  case h_nil_right =>  simp only [ne_eq, brak_neq_zero, not_false_eq_true, graft_nil_eq_self, prune_raw_idem, implies_true]
  case h_cons_cons =>
    intro x y xs ys hx hxs
    simp only [prune_raw, graft_raw, brak.injEq, graft_list, prune_list, List.cons.injEq] at hxs ⊢
    exact ⟨hx, hxs⟩

-- this should be enough to prove distrib lattice but lean doesnt have the equivalence :////

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


end QProd
