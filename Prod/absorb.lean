import Prod.quot_defs
import Prod.prune_basic
import Prod.graft_basic

namespace RawProd

theorem distrib : ∀ x y z, x ⊓ (y ⊔ z) = (x ⊓ y) ⊔ (x ⊓ z) := by
  apply RawProd.induction_list₃
  case h_zero_left => simp only [zero_prune_eq_zero, graft_zero_eq_self, implies_true]
  case h_zero_mid => simp only [zero_graft_eq_self, prune_zero_eq_zero, implies_true]
  case h_zero_right => simp only [graft_zero_eq_self, prune_zero_eq_zero, implies_true]
  case h_nil_left => simp only [ne_eq, brak_graft_brak_neq_zero, not_false_eq_true, nil_prune_eq_nil, brak_neq_zero, graft_nil_eq_self, implies_true]
  case h_nil_mid => simp only [ne_eq, brak_neq_zero, not_false_eq_true, nil_prune_eq_self, prune_nil_eq_nil, brak_prune_brak_neq_zero, implies_true]
  case h_nil_right => simp only [ne_eq, brak_neq_zero, not_false_eq_true, graft_nil_eq_self, prune_nil_eq_nil, brak_prune_brak_neq_zero, implies_true]
  case h_cons_cons_cons =>
    intros _ _ _ _ _ _ hx hxs
    simp only [graft_raw, padWith, List.zipWithAll_cons_cons, Option.getD_some, prune_raw, List.zipWith_cons_cons, brak.injEq, List.cons.injEq] at hxs ⊢
    exact ⟨hx, hxs⟩


-- literally just copied and paste commutativity proof and reran simps
theorem absorption1 : ∀ x y, x ⊔ (x ⊓ y) = x := by
  apply RawProd.induction_list₂
  case h_zero_left => simp only [zero_prune_eq_zero, graft_zero_eq_self, implies_true]
  case h_zero_right => simp only [prune_zero_eq_zero, graft_zero_eq_self, implies_true]
  case h_nil_left => simp only [ne_eq, brak_neq_zero, not_false_eq_true, nil_prune_eq_nil, graft_nil_eq_self, implies_true]
  case h_nil_right => simp only [ne_eq, brak_neq_zero, not_false_eq_true, prune_nil_eq_nil, graft_nil_eq_self, implies_true]
  case h_cons_cons =>
    intro x y xs ys hx hxs
    simp only [prune_raw, graft_raw, padWith, brak.injEq, List.zipWith_cons_cons, List.zipWithAll_cons_cons, Option.getD_some, List.cons.injEq] at hxs ⊢
    exact ⟨hx, hxs⟩

--even easier
theorem absorption2 : ∀ x y, x ⊓ (x ⊔ y) = x := by
  apply RawProd.induction_list₂
  case h_zero_left => simp only [zero_graft_eq_self, zero_prune_eq_zero, implies_true]
  case h_zero_right =>  intro x; simp only [graft_zero_eq_self, prune_raw_idem]
  case h_nil_left => simp only [ne_eq, brak_neq_zero, not_false_eq_true, nil_prune_eq_self, nil_prune_eq_nil, implies_true]
  case h_nil_right =>  simp only [ne_eq, brak_neq_zero, not_false_eq_true, graft_nil_eq_self, prune_raw_idem, implies_true]
  case h_cons_cons =>
    intro x y xs ys hx hxs
    simp only [prune_raw, graft_raw, padWith, brak.injEq, List.zipWith_cons_cons, List.zipWithAll_cons_cons, Option.getD_some, List.cons.injEq] at hxs ⊢
    exact ⟨hx, hxs⟩

-- this should be enough to prove distrib lattice but lean doesnt have the equivalence :////

end RawProd
