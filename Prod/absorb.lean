import Prod.quot_defs
import Prod.prune_basic
import Prod.graft_basic

namespace RawProd

theorem distrib : ∀ x y z, x ⊓ (y ⊔ z) = (x ⊓ y) ⊔ (x ⊓ z) := by
  apply RawProd.strong_induction₃
  case h_zero_left => simp only [zero_prune_eq_zero, graft_zero_eq_self, implies_true]
  case h_zero_mid => simp only [zero_graft_eq_self, prune_zero_eq_zero, implies_true]
  case h_zero_right => simp only [graft_zero_eq_self, prune_zero_eq_zero, implies_true]
  case h_brak_brak_brak =>
    intros xs ys zs ih
    induction xs generalizing ys zs with
    | nil => simp only [ne_eq, brak_graft_brak_neq_zero, not_false_eq_true, nil_prune_eq_nil, reduceCtorEq, graft_nil_eq_self]
    | cons x' xx ihxx =>
      cases ys with
      | nil =>
        simp only [ne_eq, reduceCtorEq, not_false_eq_true, nil_prune_eq_self, prune_nil_eq_nil, brak_prune_brak_neq_zero]
      | cons y yy =>
        cases zs with
        | nil => simp only [ne_eq, reduceCtorEq, not_false_eq_true, graft_nil_eq_self, prune_nil_eq_nil, brak_prune_brak_neq_zero]
        | cons z zz =>
          simp only [graft_raw, padWith, List.zipWithAll_cons_cons, Option.getD_some, prune_raw, List.zipWith_cons_cons, brak.injEq, List.cons.injEq]
          constructor
          . apply ih <;> simp only [List.mem_cons, true_or]
          . simp only [graft_raw, padWith, prune_raw, brak.injEq] at ihxx
            simp_all only [List.mem_cons, forall_eq_or_imp, implies_true]


-- literally just copied and paste commutativity proof and reran simps
theorem absorption1 : ∀ x y, x ⊔ (x ⊓ y) = x := by
  apply RawProd.strong_induction₂
  case h_zero_left => simp only [zero_prune_eq_zero, graft_zero_eq_self, implies_true]
  case h_zero_right => simp only [prune_zero_eq_zero, graft_zero_eq_self, implies_true]
  case h_brak_brak =>
    intro xs ys ih
    induction xs generalizing ys with
    | nil => simp only [ne_eq, reduceCtorEq, not_false_eq_true, nil_prune_eq_nil, graft_nil_eq_self]
    | cons z zs ihz =>
      cases ys with
      | nil => simp only [ne_eq, reduceCtorEq, not_false_eq_true, prune_nil_eq_nil, graft_nil_eq_self]
      | cons y yy =>
        simp only [prune_raw, padWith, List.zipWith_cons_cons, graft_raw, List.zipWithAll_cons_cons, Option.getD_some, brak.injEq, List.cons.injEq]
        constructor
        . apply ih <;> simp only [List.mem_cons, true_or]
        . simp only [graft_raw, prune_raw, brak.injEq] at ihz;
          apply ihz
          intro x hx y' hy'
          apply ih <;> simp only [List.mem_cons] <;> right; exact hx; exact hy'

--even easier
theorem absorption2 : ∀ x y, x ⊓ (x ⊔ y) = x := by
  apply RawProd.strong_induction₂
  case h_zero_left => simp only [zero_graft_eq_self, zero_prune_eq_zero, implies_true]
  case h_zero_right => intro x; simp only [graft_zero_eq_self, prune_raw_idem]
  case h_brak_brak =>
    intro xs ys ih
    induction xs generalizing ys with
    | nil => simp only [ne_eq, reduceCtorEq, not_false_eq_true, nil_prune_eq_self, nil_prune_eq_nil]
    | cons z zs ihz =>
      cases ys with
      | nil => simp only [ne_eq, reduceCtorEq, not_false_eq_true, graft_nil_eq_self, prune_raw_idem]
      | cons y yy =>
        simp only [prune_raw, padWith, List.zipWith_cons_cons, graft_raw, List.zipWithAll_cons_cons, Option.getD_some, brak.injEq, List.cons.injEq]
        constructor
        . apply ih <;> simp only [List.mem_cons, true_or]
        . simp only [graft_raw, prune_raw, brak.injEq] at ihz;
          apply ihz
          intro x hx y' hy'
          apply ih <;> simp only [List.mem_cons] <;> right; exact hx; exact hy'

-- this should be enough to prove distrib lattice but lean doesnt have the equivalence :////

end RawProd
