import Prod.quot_defs
import Mathlib.Data.List.Basic

namespace RawProd


def graft_raw : RawProd → RawProd → RawProd
  | brak xs, brak ys =>
      brak (padWith graft_raw xs ys)
  | zero, y => y
  | x, zero => x
termination_by x y => x.size + y.size
decreasing_by
  sorry


infixl:70 " ⊔ " => graft_raw


@[simp]
lemma zero_graft_eq_self (x : RawProd) : zero ⊔ x = x := by simp only [graft_raw]

@[simp]
lemma graft_zero_eq_self (x : RawProd) : x ⊔ zero = x := by
  cases x <;> simp [graft_raw]



@[simp]
lemma brak_graft_nil_eq_self (xs : List RawProd) : (brak xs) ⊔ (brak []) = brak xs := by
    simp only [graft_raw, padWith]
    simp_all only [List.zipWithAll_nil, Option.getD_some, Option.getD_none, graft_zero_eq_self, List.map_id_fun', id_eq]


@[simp]
lemma brak_nil_graft_eq_self (xs : List RawProd) : (brak []) ⊔ (brak xs) = brak xs := by
  simp only [graft_raw, padWith]
  cases xs
  . simp only [List.zipWithAll_nil, Option.getD_some, Option.getD_none, graft_zero_eq_self,
    List.map_nil]
  . simp only [List.nil_zipWithAll, Option.getD_none, Option.getD_some, zero_graft_eq_self,
    List.map_cons, List.map_id_fun', id_eq]


@[simp]
lemma graft_nil_eq_self (x : RawProd) (hnz: x ≠ zero) : x ⊔ (brak []) = x := by
  -- how does simp not work?
    cases x
    . simp only [zero_graft_eq_self, reduceCtorEq]; contradiction
    . simp only [brak_graft_nil_eq_self]


@[simp]
lemma nil_prune_eq_self (x : RawProd) (hnx : x ≠ zero) : (brak []) ⊔ x = x := by
  cases x
  . simp only [graft_zero_eq_self, reduceCtorEq]; contradiction
  . simp only [brak_nil_graft_eq_self]


@[aesop unsafe]
lemma brak_graft_brak_neq_zero (xs ys : List RawProd) : (brak xs) ⊔ (brak ys) ≠ zero := by
  simp only [graft_raw, ne_eq, reduceCtorEq, not_false_eq_true]




theorem graft_raw_idem (x : RawProd) : x ⊔ x = x := by
  induction x using RawProd.induction with
  | h_zero => apply graft_zero_eq_self
  | h_brak xs ih =>
    induction xs with
    | nil => apply brak_graft_nil_eq_self
    | cons y ys ihy =>
      simp_all only [List.mem_cons, or_true, implies_true, forall_const, forall_eq_or_imp]
      obtain ⟨left, right⟩ := ih
      simp only [graft_raw, padWith, List.zipWithAll_cons_cons, Option.getD_some, brak.injEq, List.cons.injEq]
      constructor
      . exact left
      . simp only [graft_raw, brak.injEq] at ihy
        exact ihy



theorem graft_raw_comm : ∀ x y, x ⊔ y = y ⊔ x := by
  apply RawProd.strong_induction₂
  case h_zero_left => simp only [zero_graft_eq_self, graft_zero_eq_self, implies_true]
  case h_zero_right => simp only [zero_graft_eq_self, graft_zero_eq_self, implies_true]
  case h_brak_brak =>
    intro xs ys ih
    induction xs generalizing ys with
    | nil => simp only [ne_eq, reduceCtorEq, not_false_eq_true, nil_prune_eq_self, graft_nil_eq_self]
    | cons z zs ihz =>
      cases ys with
      | nil => simp only [ne_eq, reduceCtorEq, not_false_eq_true, graft_nil_eq_self, nil_prune_eq_self]
      | cons y yy =>
        simp only [graft_raw, padWith, List.zipWithAll_cons_cons, Option.getD_some, brak.injEq, List.cons.injEq]
        constructor
        . apply ih <;> simp only [List.mem_cons, true_or]
        . simp only [graft_raw, brak.injEq] at ihz;
          apply ihz
          intro x hx y' hy'
          apply ih <;> simp only [List.mem_cons] <;> right; exact hx; exact hy'


theorem graft_raw_assoc : ∀ x y z, x ⊔ (y ⊔ z) = (x ⊔ y) ⊔ z := by
  apply RawProd.strong_induction₃
  case h_zero_left => simp only [zero_graft_eq_self, implies_true]
  case h_zero_mid => simp only [zero_graft_eq_self, graft_zero_eq_self, implies_true]
  case h_zero_right => simp only [graft_zero_eq_self, implies_true]
  case h_brak_brak_brak =>
    intros xs ys zs ih
    induction xs generalizing ys zs with
    | nil =>
      simp only [ne_eq, brak_graft_brak_neq_zero, not_false_eq_true, nil_prune_eq_self, reduceCtorEq]
    | cons x' xx ihxx =>
      cases ys with
      | nil =>
        simp only [ne_eq, reduceCtorEq, not_false_eq_true, nil_prune_eq_self, graft_nil_eq_self]
      | cons y yy =>
        simp only [graft_raw, padWith, List.zipWithAll_cons_cons, Option.getD_some, brak.injEq]
        cases zs with
        | nil => simp only [List.zipWithAll_nil, Option.getD_some, Option.getD_none, graft_zero_eq_self, List.map_cons, List.map_id_fun', id_eq, List.zipWithAll_cons_cons]
        | cons z zz =>
          simp only [List.zipWithAll_cons_cons, Option.getD_some, List.cons.injEq]
          constructor
          . apply ih <;> simp only [List.mem_cons, true_or]
          . simp only [graft_raw, brak.injEq] at ihxx
            apply ihxx
            simp_all only [List.mem_cons, forall_eq_or_imp, implies_true]



end RawProd
