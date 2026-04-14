import Prod.quot_defs
import Mathlib.Data.List.Basic

namespace RawProd


mutual
  def graft_raw : RawProd → RawProd → RawProd
    | brak xs, brak ys => brak (graft_list xs ys)
    | zero, y => y
    | x, zero => x

  def graft_list : List RawProd → List RawProd → List RawProd
    | [], ys => ys
    | xs, [] => xs
    | x :: xs, y :: ys => (graft_raw x y) :: graft_list xs ys
end


infixl:70 " ⊔ " => graft_raw


@[simp]
lemma zero_graft_eq_self (x : RawProd) : zero ⊔ x = x := by simp only [graft_raw]

@[simp]
lemma graft_zero_eq_self (x : RawProd) : x ⊔ zero = x := by
  cases x <;> simp only [graft_raw]



@[simp]
lemma graft_list_nil_right (xs : List RawProd) : graft_list xs [] = xs := by
  cases xs <;> rfl

@[simp]
lemma graft_list_nil_left (xs : List RawProd) : graft_list [] xs = xs := by
  simp only [graft_list]

@[simp]
lemma brak_graft_nil_eq_self {xs : List RawProd} : (brak xs) ⊔ nil = brak xs := by
  simp only [graft_raw, graft_list_nil_right]


@[simp]
lemma brak_nil_graft_eq_self (xs : List RawProd) : nil ⊔ (brak xs) = brak xs := by
  simp only [graft_raw, graft_list_nil_left]


@[simp]
lemma graft_nil_eq_self (x : RawProd) (hnz: x ≠ zero) : x ⊔ nil = x := by
  -- how does simp not work?
    cases x
    . simp only [zero_graft_eq_self, reduceCtorEq]; contradiction
    . simp only [brak_graft_nil_eq_self]


@[simp]
lemma nil_graft_eq_self {x : RawProd} (hnx : x ≠ zero) : nil ⊔ x = x := by
  cases x
  . simp only [graft_zero_eq_self, reduceCtorEq]; contradiction
  . simp only [brak_nil_graft_eq_self]


@[aesop unsafe]
lemma brak_graft_brak_neq_zero (xs ys : List RawProd) : (brak xs) ⊔ (brak ys) ≠ zero := by
  simp only [graft_raw, ne_eq, reduceCtorEq, not_false_eq_true]


lemma cons_graft_cons {xs ys : List RawProd} {x y : RawProd} : (brak (x::xs)) ⊔ (brak (y::ys)) = brak ((x ⊔ y) :: graft_list xs ys) := by
  simp only [graft_raw, graft_list]


theorem graft_raw_idem (x : RawProd) : x ⊔ x = x := by
  induction x using RawProd.induction_list with
  | h_zero => apply graft_zero_eq_self
  | h_nil => exact brak_graft_nil_eq_self
  | h_cons x xs hx hxs =>
      simp only [graft_raw, graft_list, brak.injEq, List.cons.injEq] at hxs ⊢
      exact ⟨hx, hxs⟩


theorem graft_raw_comm : ∀ x y, x ⊔ y = y ⊔ x := by
  apply RawProd.induction_list₂
  case h_zero_left => simp only [zero_graft_eq_self, graft_zero_eq_self, implies_true]
  case h_zero_right => simp only [zero_graft_eq_self, graft_zero_eq_self, implies_true]
  case h_nil_left => simp only [ne_eq, brak_neq_zero, not_false_eq_true, nil_graft_eq_self, graft_nil_eq_self, implies_true]
  case h_nil_right => simp only [ne_eq, brak_neq_zero, not_false_eq_true, graft_nil_eq_self, nil_graft_eq_self, implies_true]
  case h_cons_cons =>
    intro x y xs ys hx hxs
    simp only [graft_raw, graft_list, brak.injEq, List.cons.injEq] at hxs ⊢
    exact ⟨hx, hxs⟩



theorem graft_raw_assoc : ∀ x y z, (x ⊔ y) ⊔ z = x ⊔ (y ⊔ z):= by
  apply RawProd.induction_list₃
  case h_zero_left => simp only [zero_graft_eq_self, implies_true]
  case h_zero_mid => simp only [zero_graft_eq_self, graft_zero_eq_self, implies_true]
  case h_zero_right => simp only [graft_zero_eq_self, implies_true]
  case h_nil_left => simp only [ne_eq, brak_graft_brak_neq_zero, not_false_eq_true, nil_graft_eq_self, brak_neq_zero, implies_true]
  case h_nil_mid =>  simp only [ne_eq, brak_neq_zero, not_false_eq_true, nil_graft_eq_self, graft_nil_eq_self, implies_true]
  case h_nil_right => simp only [graft_raw, graft_list_nil_right, ne_eq, brak_neq_zero, not_false_eq_true, graft_nil_eq_self, implies_true]
  case h_cons_cons_cons =>
    intros x y z xs ys zs hx hxs
    simp only [graft_raw, graft_list, brak.injEq, List.cons.injEq] at hxs ⊢
    exact ⟨hx, hxs⟩


lemma allzero_graft_eq_self {xs ys : List RawProd} (haz : allzero xs) : (brak ys).equiv (brak xs ⊔ brak ys) := by
  simp only [graft_raw]
  induction xs generalizing ys with
  | nil => simp only [graft_list]; exact equiv_refl _
  | cons x xs ih =>
    obtain ⟨hxz, hxsaz⟩ := allzero_cons haz
    subst hxz
    cases ys with
    | nil =>
      simp only [graft_list]
      exact nil_equiv_brak_iff_allzero.mpr haz
    | cons y ys =>
      simp only [graft_list, zero_graft_eq_self]
      apply cons_equiv_cons_iff.mp
      constructor
      . exact equiv_refl _
      . apply ih
        exact hxsaz



theorem graft_raw_respects_equiv {x x' y y' : RawProd} (hx : x.equiv x') (hy : y.equiv y') : (x ⊔ y).equiv (x' ⊔ y') := by
  revert x x' y y'
  apply induction_list₄
  case h_zero1 => intro x y z h1 h2; rw [equiv_zero_eq_zero h1]; simp only [zero_graft_eq_self]; exact h2
  case h_zero2 => intro x y z h1 h2; rw [zero_equiv_eq_zero h1]; simp only [zero_graft_eq_self]; exact h2
  case h_zero3 => intro x y z h1 h2; rw [equiv_zero_eq_zero h2]; simp only [graft_zero_eq_self]; exact h1
  case h_zero4 => intro x y z h1 h2; rw [zero_equiv_eq_zero h2]; simp only [graft_zero_eq_self]; exact h1
  case h_nil1 => intro xs ys zs h1 h2; simp only [brak_nil_graft_eq_self]; exact equiv_trans h2 (allzero_graft_eq_self (nil_equiv_brak_iff_allzero.mp h1))
  case h_nil2 => intro ws ys zs h1 h2; simp only [brak_nil_graft_eq_self]; have hstep : (brak ys).equiv (brak ws ⊔ brak ys) := allzero_graft_eq_self (nil_equiv_brak_iff_allzero.mp (equiv_symm h1)); exact equiv_trans (equiv_symm hstep) h2
  case h_nil3 => intro ws xs zs h1 h2; simp only [brak_graft_nil_eq_self]; have hstep : (brak xs).equiv (brak zs ⊔ brak xs) := allzero_graft_eq_self (nil_equiv_brak_iff_allzero.mp h2); rw [graft_raw_comm (brak zs) (brak xs)] at hstep; exact equiv_trans h1 hstep
  case h_nil4 =>
    intro ws xs ys h1 h2; simp only [brak_graft_nil_eq_self]
    have hstep : (brak ws).equiv (brak ys ⊔ brak ws) := allzero_graft_eq_self (nil_equiv_brak_iff_allzero.mp (equiv_symm h2))
    rw [graft_raw_comm (brak ys) (brak ws)] at hstep
    exact equiv_trans (equiv_symm hstep) h1
  case h_cons_cons_cons_cons =>
    intro w x y z ws xs ys zs h hs h1 h2
    simp only [cons_graft_cons]
    obtain ⟨h1h, h1t⟩ := cons_equiv_cons_iff.mpr h1
    obtain ⟨h2h, h2t⟩ := cons_equiv_cons_iff.mpr h2
    apply cons_equiv_cons_iff.mp; constructor
    . apply h; exact h1h; exact h2h
    . simp only [graft_raw] at hs
      apply hs; exact h1t; exact h2t


end RawProd


namespace QProd

open RawProd


def graft (x y : QProd) : QProd :=
  Quotient.liftOn₂ x y (fun a b => mk (RawProd.graft_raw a b)) fun _ _ _ _ hx hy =>
    Quotient.sound (RawProd.graft_raw_respects_equiv hx hy)



infixl:70 " ⊔ " => graft

/-- Core computation rule: graft reduces to mk on representatives. -/
lemma graft_mk_mk (x y : RawProd) : (mk x) ⊔ (mk y) = mk (x ⊔ y) := rfl

theorem graft_idem : ∀ x : QProd, x ⊔ x = x :=
  by apply lift_eq₁ graft_raw_idem

theorem graft_comm : ∀ x y  : QProd,  x ⊔ y = y ⊔ x :=
  by apply lift_eq₂ graft_raw_comm

theorem graft_assoc : ∀ x y z : QProd,  (x ⊔ y) ⊔ z = x ⊔ (y ⊔ z) :=
  by apply lift_eq₃ graft_raw_assoc

end QProd
