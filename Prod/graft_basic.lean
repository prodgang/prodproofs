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


lemma cons_graft_cons {xs ys : List RawProd} {x y : RawProd} : (brak (x::xs)) ⊔ (brak (y::ys)) = brak ((x ⊔ y)::(padWith graft_raw xs ys)) := by
  simp only [graft_raw, brak.injEq]
  sorry


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


theorem graft_raw_respects_equiv {x x' y y' : RawProd} (hx : x.equiv x') (hy : y.equiv y') : (x ⊔ y).equiv (x' ⊔ y') := by
  revert x x' y y'
  apply induction_list₄
  case h_zero1 => intro x y z h1 h2; rw [equiv_zero_eq_zero h1]; simp only [zero_graft_eq_self]; exact h2
  case h_zero2 => intro x y z h1 h2; rw [zero_equiv_eq_zero h1]; simp only [zero_graft_eq_self]; exact h2
  case h_zero3 => intro x y z h1 h2; rw [equiv_zero_eq_zero h2]; simp only [graft_zero_eq_self]; exact h1
  case h_zero4 => intro x y z h1 h2; rw [zero_equiv_eq_zero h2]; simp only [graft_zero_eq_self]; exact h1
  case h_nil1 => sorry -- intros; simp [ne_eq, brak_neq_zero, not_false_eq_true]; apply prune_raw_trim_equiv; assumption;
  case h_nil2 => sorry
  case h_nil3 => sorry
  case h_nil4 => sorry
  case h_cons_cons_cons_cons =>
    intro w x y z ws xs ys zs h hs h1 h2
    simp only [cons_graft_cons]
    obtain ⟨h1h, h1t⟩ := cons_equiv_cons_iff.mpr h1
    obtain ⟨h2h, h2t⟩ := cons_equiv_cons_iff.mpr h2
    apply cons_equiv_cons_iff.mp; constructor
    . apply h; exact h1h; exact h2h
    . simp [graft_raw] at hs
      apply hs; exact h1t; exact h2t


end RawProd


namespace QProd

open RawProd

-- def graft (x y : QProd ): QProd := Quotient.liftOn₂ x y (fun x y => mk (RawProd.graft_raw x y)) (by
--   intro x₁ x₂ y₁ y₂ h₁ h₂
--   simp only
--   revert h₁ h₂
--   apply Quotient.indu;
--   sorry
-- )

def graft (x y : QProd) : QProd :=
  Quotient.liftOn₂ x y (fun a b => mk (RawProd.graft_raw a b)) fun _ _ _ _ hx hy =>
    Quotient.sound (RawProd.graft_raw_respects_equiv hx hy)


-- def graft (x y : QProd) : QProd :=
--   mk (RawProd.graft_raw (rep x) (rep y))
--   --mk (RawProd.normalize (RawProd.graft_raw (rep x) (rep y)))



infixl:70 " ⊔ " => graft

theorem graft_idem {x : QProd} : x ⊔ x = x := by

  revert x
  apply Quotient.ind
  intro x
  apply Quotient.sound
  rw [graft_raw_idem]
  rfl

theorem graft_comm {x y : QProd } : x ⊔ y = y ⊔ x := by
  revert x y
  apply Quotient.ind₂
  intro x y
  apply Quotient.sound
  rw [graft_raw_comm]
  rfl


theorem graft_assoc {x y z : QProd } : x ⊔ (y ⊔ z) = (x ⊔ y) ⊔ z := by
  refine Quotient.inductionOn₃ x y z ?_
  intro a b c
  apply Quotient.sound
  rw [graft_raw_assoc]
  rfl

end QProd
