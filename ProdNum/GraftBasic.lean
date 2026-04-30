/-
Copyright (c) 2024 Edwin Agnew. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Edwin Agnew
-/
import ProdNum.QuotDefs
import Mathlib.Data.List.Basic

/-!
# Productive Numbers — Graft (Join) Operation

Defines the **graft** operation `⊔` on `PreProdNum` and lifts it to `ProdNum`.
Graft is the pointwise join of two lists, zero-padded on the shorter side:
`brak xs ⊔ brak ys = brak (zipWith (⊔) xs ys)` where the shorter list is padded with zeros.

## Main definitions

- `PreProdNum.graft`, `PreProdNum.graft_list`: the mutual recursive definition
- `ProdNum.graft`: the lifted version, with notation `⊔`

## Main results

- `graft_idem`, `graft_comm`, `graft_assoc`: algebraic laws on `PreProdNum`
- `ProdNum.graft_idem`, `ProdNum.graft_comm`, `ProdNum.graft_assoc`: lifted laws
-/

namespace PreProdNum


mutual
  def graft : PreProdNum → PreProdNum → PreProdNum
    | brak xs, brak ys => brak (graft_list xs ys)
    | zero, y => y
    | x, zero => x

  def graft_list : List PreProdNum → List PreProdNum → List PreProdNum
    | [], ys => ys
    | xs, [] => xs
    | x :: xs, y :: ys => (graft x y) :: graft_list xs ys
end


infixl:70 " ⊔ " => graft


@[simp]
lemma zero_graft (x : PreProdNum) : zero ⊔ x = x := by simp only [graft]

@[simp]
lemma graft_zero (x : PreProdNum) : x ⊔ zero = x := by
  cases x <;> simp only [graft]



@[simp]
lemma graft_list_nil_right (xs : List PreProdNum) : graft_list xs [] = xs := by
  cases xs <;> rfl

@[simp]
lemma graft_list_nil_left (xs : List PreProdNum) : graft_list [] xs = xs := by
  simp only [graft_list]

@[simp]
lemma brak_graft_nil_eq_self {xs : List PreProdNum} : (brak xs) ⊔ nil = brak xs := by
  simp only [graft, graft_list_nil_right]


@[simp]
lemma brak_nil_graft_eq_self (xs : List PreProdNum) : nil ⊔ (brak xs) = brak xs := by
  simp only [graft, graft_list_nil_left]


@[simp]
lemma graft_nil_eq_self (x : PreProdNum) (hnz: x ≠ zero) : x ⊔ nil = x := by
  cases x
  · simp only [zero_graft, reduceCtorEq]; contradiction
  · simp only [brak_graft_nil_eq_self]


@[simp]
lemma nil_graft_eq_self {x : PreProdNum} (hnx : x ≠ zero) : nil ⊔ x = x := by
  cases x
  . simp only [graft_zero, reduceCtorEq]; contradiction
  . simp only [brak_nil_graft_eq_self]



lemma brak_graft_brak_ne_zero (xs ys : List PreProdNum) : (brak xs) ⊔ (brak ys) ≠ zero := by
  simp only [graft, ne_eq, reduceCtorEq, not_false_eq_true]


lemma cons_graft_cons {xs ys : List PreProdNum} {x y : PreProdNum} : (brak (x::xs)) ⊔ (brak (y::ys)) = brak ((x ⊔ y) :: graft_list xs ys) := by
  simp only [graft, graft_list]

lemma get_graft_list (xs ys : List PreProdNum) (i : ℕ) :
    get (graft_list xs ys) i = graft (get xs i) (get ys i) := by
  induction xs generalizing ys i with
  | nil => simp only [graft_list, get_nil, zero_graft]
  | cons xh xt ih =>
    cases ys with
    | nil => simp only [graft_list, get_nil, graft_zero]
    | cons yh yt =>
      simp only [graft_list]; cases i with
      | zero => simp only [get_cons_zero]
      | succ n => simp only [get_cons_succ, ih]

theorem graft_idem (x : PreProdNum) : x ⊔ x = x := by
  induction x using PreProdNum.induction_list with
  | h_zero => apply graft_zero
  | h_nil => exact brak_graft_nil_eq_self
  | h_cons x xs hx hxs =>
      simp only [graft, graft_list, brak.injEq, List.cons.injEq] at hxs ⊢
      exact ⟨hx, hxs⟩


theorem graft_comm : ∀ x y, x ⊔ y = y ⊔ x := by
  apply PreProdNum.induction_list₂
  case h_zero_left => simp only [zero_graft, graft_zero, implies_true]
  case h_zero_right => simp only [zero_graft, graft_zero, implies_true]
  case h_nil_left => simp only [ne_eq, brak_ne_zero, not_false_eq_true, nil_graft_eq_self, graft_nil_eq_self, implies_true]
  case h_nil_right => simp only [ne_eq, brak_ne_zero, not_false_eq_true, graft_nil_eq_self, nil_graft_eq_self, implies_true]
  case h_cons_cons =>
    intro x y xs ys hx hxs
    simp only [graft, graft_list, brak.injEq, List.cons.injEq] at hxs ⊢
    exact ⟨hx, hxs⟩



theorem graft_assoc : ∀ x y z, (x ⊔ y) ⊔ z = x ⊔ (y ⊔ z):= by
  apply PreProdNum.induction_list₃
  case h_zero_left => simp only [zero_graft, implies_true]
  case h_zero_mid => simp only [zero_graft, graft_zero, implies_true]
  case h_zero_right => simp only [graft_zero, implies_true]
  case h_nil_left => simp only [ne_eq, brak_graft_brak_ne_zero, not_false_eq_true, nil_graft_eq_self, brak_ne_zero, implies_true]
  case h_nil_mid =>  simp only [ne_eq, brak_ne_zero, not_false_eq_true, nil_graft_eq_self, graft_nil_eq_self, implies_true]
  case h_nil_right => simp only [graft, graft_list_nil_right, ne_eq, brak_ne_zero, not_false_eq_true, graft_nil_eq_self, implies_true]
  case h_cons_cons_cons =>
    intros x y z xs ys zs hx hxs
    simp only [graft, graft_list, brak.injEq, List.cons.injEq] at hxs ⊢
    exact ⟨hx, hxs⟩


lemma allzero_graft {xs ys : List PreProdNum} (haz : allzero xs) : (brak ys).equiv (brak xs ⊔ brak ys) := by
  simp only [graft]
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
      simp only [graft_list, zero_graft]
      apply cons_equiv_cons_iff.mp
      constructor
      . exact equiv_refl _
      . apply ih
        exact hxsaz



theorem graft_respects_equiv {x x' y y' : PreProdNum} (hx : x.equiv x') (hy : y.equiv y') : (x ⊔ y).equiv (x' ⊔ y') := by
  revert x x' y y'
  apply induction_list₄
  case h_zero1 => intro x y z h1 h2; rw [equiv_zero_eq_zero h1]; simp only [zero_graft]; exact h2
  case h_zero2 => intro x y z h1 h2; rw [zero_equiv_eq_zero h1]; simp only [zero_graft]; exact h2
  case h_zero3 => intro x y z h1 h2; rw [equiv_zero_eq_zero h2]; simp only [graft_zero]; exact h1
  case h_zero4 => intro x y z h1 h2; rw [zero_equiv_eq_zero h2]; simp only [graft_zero]; exact h1
  case h_nil1 => intro xs ys zs h1 h2; simp only [brak_nil_graft_eq_self]; exact equiv_trans h2 (allzero_graft (nil_equiv_brak_iff_allzero.mp h1))
  case h_nil2 => intro ws ys zs h1 h2; simp only [brak_nil_graft_eq_self]; have hstep : (brak ys).equiv (brak ws ⊔ brak ys) := allzero_graft (nil_equiv_brak_iff_allzero.mp (equiv_symm h1)); exact equiv_trans (equiv_symm hstep) h2
  case h_nil3 => intro ws xs zs h1 h2; simp only [brak_graft_nil_eq_self]; have hstep : (brak xs).equiv (brak zs ⊔ brak xs) := allzero_graft (nil_equiv_brak_iff_allzero.mp h2); rw [graft_comm (brak zs) (brak xs)] at hstep; exact equiv_trans h1 hstep
  case h_nil4 =>
    intro ws xs ys h1 h2; simp only [brak_graft_nil_eq_self]
    have hstep : (brak ws).equiv (brak ys ⊔ brak ws) := allzero_graft (nil_equiv_brak_iff_allzero.mp (equiv_symm h2))
    rw [graft_comm (brak ys) (brak ws)] at hstep
    exact equiv_trans (equiv_symm hstep) h1
  case h_cons_cons_cons_cons =>
    intro w x y z ws xs ys zs h hs h1 h2
    simp only [cons_graft_cons]
    obtain ⟨h1h, h1t⟩ := cons_equiv_cons_iff.mpr h1
    obtain ⟨h2h, h2t⟩ := cons_equiv_cons_iff.mpr h2
    apply cons_equiv_cons_iff.mp; constructor
    . apply h; exact h1h; exact h2h
    . simp only [graft] at hs
      apply hs; exact h1t; exact h2t


end PreProdNum


namespace ProdNum

def graft (x y : ProdNum) : ProdNum :=
  Quotient.liftOn₂ x y (fun a b => mk (PreProdNum.graft a b)) fun _ _ _ _ hx hy =>
    Quotient.sound (PreProdNum.graft_respects_equiv hx hy)

infixl:70 " ⊔ " => graft

/-- Core computation rule: graft reduces to mk on representatives. -/
lemma graft_mk_mk (x y : PreProdNum) : (mk x) ⊔ (mk y) = mk (x ⊔ y) := rfl

theorem graft_idem : ∀ x : ProdNum, x ⊔ x = x :=
  by apply lift_eq₁ PreProdNum.graft_idem

theorem graft_comm : ∀ x y  : ProdNum,  x ⊔ y = y ⊔ x :=
  by apply lift_eq₂ PreProdNum.graft_comm

theorem graft_assoc : ∀ x y z : ProdNum,  (x ⊔ y) ⊔ z = x ⊔ (y ⊔ z) :=
  by apply lift_eq₃ PreProdNum.graft_assoc

end ProdNum
