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
lemma brak_graft_nil_eq_self {xs : List RawProd} : (brak xs) ⊔ (brak []) = brak xs := by
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
lemma nil_prune_eq_self {x : RawProd} (hnx : x ≠ zero) : (brak []) ⊔ x = x := by
  cases x
  . simp only [graft_zero_eq_self, reduceCtorEq]; contradiction
  . simp only [brak_nil_graft_eq_self]


@[aesop unsafe]
lemma brak_graft_brak_neq_zero (xs ys : List RawProd) : (brak xs) ⊔ (brak ys) ≠ zero := by
  simp only [graft_raw, ne_eq, reduceCtorEq, not_false_eq_true]




theorem graft_raw_idem (x : RawProd) : x ⊔ x = x := by
  induction x using RawProd.induction_list with
  | h_zero => apply graft_zero_eq_self
  | h_nil => exact brak_graft_nil_eq_self
  | h_cons x xs hx hxs =>
      simp only [graft_raw, padWith, List.zipWithAll_cons_cons, Option.getD_some, brak.injEq, List.cons.injEq]  at hxs ⊢
      exact ⟨hx, hxs⟩


theorem graft_raw_comm : ∀ x y, x ⊔ y = y ⊔ x := by
  apply RawProd.induction_list₂
  case h_zero_left => simp only [zero_graft_eq_self, graft_zero_eq_self, implies_true]
  case h_zero_right => simp only [zero_graft_eq_self, graft_zero_eq_self, implies_true]
  case h_nil_left => simp only [ne_eq, brak_neq_zero, not_false_eq_true, nil_prune_eq_self, graft_nil_eq_self, implies_true]
  case h_nil_right => simp only [ne_eq, brak_neq_zero, not_false_eq_true, graft_nil_eq_self, nil_prune_eq_self, implies_true]
  case h_cons_cons =>
    intro x y xs ys hx hxs
    simp only [graft_raw, padWith, List.zipWithAll_cons_cons, Option.getD_some, brak.injEq, List.cons.injEq] at hxs ⊢
    exact ⟨hx, hxs⟩



theorem graft_raw_assoc : ∀ x y z, x ⊔ (y ⊔ z) = (x ⊔ y) ⊔ z := by
  apply RawProd.induction_list₃
  case h_zero_left => simp only [zero_graft_eq_self, implies_true]
  case h_zero_mid => simp only [zero_graft_eq_self, graft_zero_eq_self, implies_true]
  case h_zero_right => simp only [graft_zero_eq_self, implies_true]
  case h_nil_left => simp only [ne_eq, brak_graft_brak_neq_zero, not_false_eq_true, nil_prune_eq_self, brak_neq_zero, implies_true]
  case h_nil_mid =>  simp only [ne_eq, brak_neq_zero, not_false_eq_true, nil_prune_eq_self, graft_nil_eq_self, implies_true]
  case h_nil_right => simp only [ne_eq, brak_neq_zero, not_false_eq_true, graft_nil_eq_self, graft_raw, padWith, implies_true]
  case h_cons_cons_cons =>
    intros x y z xs ys zs hx hxs
    simp only [graft_raw, padWith, List.zipWithAll_cons_cons, Option.getD_some, brak.injEq, List.cons.injEq]  at hxs ⊢
    exact ⟨hx, hxs⟩



end RawProd


namespace QProd


def graft (x y : QProd) : QProd :=
  mk (RawProd.graft_raw (rep x) (rep y))
  --mk (RawProd.normalize (RawProd.graft_raw (rep x) (rep y)))


infixl:70 " ⊔ " => graft

theorem graft_idem {x : QProd} : x ⊔ x = x := by
  dsimp [graft]
  rw [RawProd.graft_raw_idem]
  simp only [mk_rep_eq]

theorem graft_comm {x y : QProd } : x ⊔ y = y ⊔ x := by
  dsimp [graft]
  rw [RawProd.graft_raw_comm]

lemma graft_rep_rep (x y : QProd ) : x.rep ⊔ y.rep = (x ⊔ y).rep := by -- not gonna be true for prune?
  dsimp [rep]
-- ⊢ Quotient.lift RawProd.normalize RawProd.equiv_normalize_eq x ⊔
--     Quotient.lift RawProd.normalize RawProd.equiv_normalize_eq y =
--   Quotient.lift RawProd.normalize RawProd.equiv_normalize_eq (x ⊔ y)
  sorry

theorem graft_assoc {x y z : QProd } : x ⊔ (y ⊔ z) = (x ⊔ y) ⊔ z := by
  dsimp [graft]
  rw [(graft_rep_rep x y), (graft_rep_rep y z)]
  simp only [mk_rep_eq]
  rw [← (graft_rep_rep x y), ← (graft_rep_rep y z)]
  simp [RawProd.graft_raw_assoc]

end QProd
