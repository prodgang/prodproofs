/-
Copyright (c) 2024 Edwin Agnew. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Edwin Agnew
-/
import ProdNum.QuotDefs

/-!
# Productive Numbers — Prune (Meet) Operation

Defines the **prune** operation `⊓` on `PreProdNum` and lifts it to `ProdNum`.
Prune is the pointwise meet of two lists, truncating to the shorter:
`brak xs ⊓ brak ys = brak (zipWith (⊓) xs ys)` where the result has length `min |xs| |ys|`.

## Main definitions

- `PreProdNum.prune`, `PreProdNum.prune_list`: the mutual recursive definition
- `ProdNum.prune`: the lifted version, with notation `⊓`

## Main results

- `prune_idem`, `prune_comm`, `prune_assoc`: algebraic laws on `PreProdNum`
- `ProdNum.prune_idem`, `ProdNum.prune_comm`, `ProdNum.prune_assoc`: lifted laws
-/

namespace PreProdNum

mutual
  def prune : PreProdNum → PreProdNum → PreProdNum
    | brak xs, brak ys => brak (prune_list xs ys)
    | zero, _ => zero
    | _, zero => zero

  def prune_list : List PreProdNum → List PreProdNum → List PreProdNum
    | [], _ => []
    | _, [] => []
    | x :: xs, y :: ys => (prune x y) :: prune_list xs ys
end


infixl:70 " ⊓ " => prune


@[simp]
lemma zero_prune (x : PreProdNum) : zero ⊓ x = zero := by simp only [prune]

@[simp]
lemma prune_zero (x : PreProdNum) : x ⊓ zero = zero := by
  cases x <;> simp only [prune]

@[simp]
lemma prune_list_nil_right (xs : List PreProdNum) : prune_list xs [] = [] := by
  cases xs <;> rfl

@[simp]
lemma prune_list_nil_left (xs : List PreProdNum) : prune_list [] xs = [] := by
  simp only [prune_list]

@[simp]
lemma brak_nil_prune_eq_nil (xs : List PreProdNum) : nil ⊓ (brak xs) = nil := by
  cases xs <;> simp only [prune, prune_list_nil_right, prune_list_nil_left]

@[simp]
lemma prune_nil_nz_eq_nil (x : PreProdNum) (hnz: x ≠ zero) : x ⊓ nil = nil := by
    cases x <;> simp only [prune, zero_ne_brak, prune_list_nil_right]
    contradiction


@[simp]
lemma prune_nil_eq_nil (xs : List PreProdNum) : (brak xs) ⊓ nil = nil := by
    cases xs <;> simp only [prune, prune_list_nil_right]


@[simp]
lemma nil_prune_nz_eq_nil (x : PreProdNum) (hnx : x ≠ zero) : nil ⊓ x = nil := by
  cases x <;> simp only [prune, zero_ne_brak, prune_list_nil_left]
  contradiction

lemma brak_prune_brak_ne_zero (xs ys : List PreProdNum) : (brak xs) ⊓ (brak ys) ≠ zero := by
  simp only [prune, ne_eq, reduceCtorEq, not_false_eq_true]

lemma cons_prune_cons {xs ys : List PreProdNum} {x y : PreProdNum} : (brak (x::xs)) ⊓ (brak (y::ys)) = brak ((x ⊓ y)::(prune_list xs ys)) := by
  simp only [prune, prune_list]

lemma get_prune_list (xs ys : List PreProdNum) (i : ℕ) :
    get (prune_list xs ys) i = prune (get xs i) (get ys i) := by
  induction xs generalizing ys i with
  | nil => simp only [prune_list, get_nil, zero_prune]
  | cons xh xt ih =>
    cases ys with
    | nil => simp only [prune_list, get_nil, prune_zero]
    | cons yh yt =>
      simp only [prune_list]; cases i with
      | zero => simp only [get_cons_zero]
      | succ n => simp only [get_cons_succ, ih]


lemma nil_prune_eq_zero_iff {y : PreProdNum} : nil ⊓ y = zero ↔ y = zero := by
  constructor
  · cases y with
    | zero => intro; rfl
    | brak ys =>
      simp only [prune, prune_list_nil_left]
      exact fun h => absurd h brak_ne_zero
  · intro h; rw [h, prune_zero]

lemma allzero_prune_eq_replicate {xs ys : List PreProdNum} (haz : allzero xs) :
    ((brak xs) ⊓ (brak ys)) = brak (List.replicate (min xs.length ys.length) zero) := by
  simp only [prune]
  induction xs generalizing ys with
  | nil => simp only [prune_list, List.length_nil, Nat.zero_min, List.replicate_zero]
  | cons x xs ih =>
    obtain ⟨hxz, hxsaz⟩ := allzero_cons haz
    subst hxz
    cases ys with
    | nil => simp only [prune_list, List.length_cons, List.length_nil, Nat.le_add_left, Nat.min_eq_right, List.replicate_zero]
    | cons y ys =>
      simp only [prune_list, zero_prune, List.length_cons]
      have hmin : min (xs.length + 1) (ys.length + 1) = min xs.length ys.length + 1 := by omega
      rw [hmin, List.replicate_succ]
      specialize ih hxsaz
      . exact ys
      simp only [brak.injEq, List.cons.injEq, true_and]
      simp only [brak.injEq] at ih
      exact ih

theorem prune_idem : ∀ x : PreProdNum, x ⊓ x = x := by
  intro x
  induction x using PreProdNum.induction_list with
  | h_zero => apply prune_zero
  | h_nil => exact prune_nil_eq_nil _
  | h_cons xs ih =>
    simp_all only [prune, brak.injEq, prune_list]


theorem prune_comm : ∀ x y : PreProdNum, x ⊓ y = y ⊓ x := by
  apply PreProdNum.induction_list₂
  case h_zero_left => simp only [zero_prune, prune_zero, implies_true]
  case h_zero_right => simp only [prune_zero, zero_prune, implies_true]
  case h_nil_left => simp only [ne_eq, brak_ne_zero, not_false_eq_true, nil_prune_nz_eq_nil, prune_nil_eq_nil, implies_true]
  case h_nil_right => simp only [ne_eq, brak_ne_zero, not_false_eq_true, prune_nil_nz_eq_nil, nil_prune_nz_eq_nil, implies_true]
  case h_cons_cons =>
    intro x y xs ys hx hxs
    simp only [prune, brak.injEq, prune_list, List.cons.injEq] at hxs ⊢
    exact ⟨hx, hxs⟩


theorem prune_assoc : ∀ x y z : PreProdNum, (x ⊓ y) ⊓ z = x ⊓ (y ⊓ z) := by
  apply PreProdNum.induction_list₃
  case h_zero_left => simp only [zero_prune, implies_true];
  case h_zero_mid => simp only [zero_prune, prune_zero, implies_true]
  case h_zero_right => simp only [prune_zero, implies_true]
  case h_nil_left => simp only [ne_eq, brak_prune_brak_ne_zero, not_false_eq_true, nil_prune_nz_eq_nil, brak_ne_zero, implies_true]
  case h_nil_mid => simp only [brak_nil_prune_eq_nil, prune_nil_eq_nil, implies_true]
  case h_nil_right => simp only [prune, prune_list_nil_right, ne_eq, brak_ne_zero, not_false_eq_true, prune_nil_nz_eq_nil, implies_true]
  case h_cons_cons_cons =>
    intros x y z xs ys zs hx hxs
    simp only [prune, brak.injEq, prune_list, List.cons.injEq] at ⊢ hxs
    exact ⟨hx, hxs⟩


lemma prune_trim_equiv {xs ys : List PreProdNum} : nil.equiv (brak xs) → nil.equiv (brak xs ⊓ brak ys) := by
  intro h1
  have haz : allzero xs := by exact nil_equiv_brak_iff_allzero.mp h1
  simp only [allzero_prune_eq_replicate haz]
  simp only [nil_equiv_brak_iff_allzero, allzero, List.length_replicate]

theorem prune_respects_equiv {x x' y y' : PreProdNum} (hx : x.equiv x') (hy : y.equiv y') : (x ⊓ y).equiv (x' ⊓ y') := by
  revert x x' y y'
  apply induction_list₄
  case h_zero1 => intro x y z h1 h2; rw [equiv_zero_eq_zero h1]; simp only [zero_prune]; rfl
  case h_zero2 => intro x y z h1 h2; rw [zero_equiv_eq_zero h1]; simp only [zero_prune]; rfl
  case h_zero3 => intro x y z h1 h2; rw [equiv_zero_eq_zero h2]; simp only [prune_zero]; rfl
  case h_zero4 => intro x y z h1 h2; rw [zero_equiv_eq_zero h2]; simp only [prune_zero]; rfl
  case h_nil1 => intros; simp only [ne_eq, brak_ne_zero, not_false_eq_true, nil_prune_nz_eq_nil]; apply prune_trim_equiv; assumption;
  case h_nil2 => intros; simp only [ne_eq, brak_ne_zero, not_false_eq_true, nil_prune_nz_eq_nil]; apply equiv_symm; apply prune_trim_equiv; apply equiv_symm; assumption;
  case h_nil3 => intros ws xs zs h1 h2; rw [prune_comm (brak xs) (brak zs)]; simp only [ne_eq, brak_ne_zero, not_false_eq_true, prune_nil_nz_eq_nil]; apply prune_trim_equiv; exact h2
  case h_nil4 => intros ws xs zs h1 h2; rw [prune_comm (brak ws) (brak zs)]; simp only [ne_eq, brak_ne_zero, not_false_eq_true, prune_nil_nz_eq_nil]; apply equiv_symm; apply prune_trim_equiv; apply equiv_symm; exact h2
  case h_cons_cons_cons_cons =>
    intro w x y z ws xs ys zs h hs h1 h2
    simp only [cons_prune_cons]
    obtain ⟨h1h, h1t⟩ := cons_equiv_cons_iff.mpr h1
    obtain ⟨h2h, h2t⟩ := cons_equiv_cons_iff.mpr h2
    apply cons_equiv_cons_iff.mp; constructor
    . apply h; exact h1h; exact h2h
    . simp only [prune] at hs
      apply hs; exact h1t; exact h2t




end PreProdNum

namespace ProdNum

/-- Lift `prune` to `ProdNum`. -/
def prune (x y : ProdNum) : ProdNum :=
  Quotient.liftOn₂ x y (fun a b => mk (PreProdNum.prune a b)) fun _ _ _ _ hx hy =>
    Quotient.sound (PreProdNum.prune_respects_equiv hx hy)

infixl:70 " ⊓ " => prune

/-- compute on `mk`ed representatives -/
lemma prune_mk_mk (x y : PreProdNum) : (mk x) ⊓ (mk y) = mk (x ⊓ y) := rfl

theorem prune_idem : ∀ q : ProdNum, q ⊓ q = q := by
  apply lift_eq₁ PreProdNum.prune_idem

theorem prune_comm : ∀ x y : ProdNum,  x ⊓ y = y ⊓ x := by
  apply lift_eq₂ PreProdNum.prune_comm

theorem prune_assoc :  ∀ x y z : ProdNum, (x ⊓ y) ⊓ z  = x ⊓ (y ⊓ z):= by
  apply lift_eq₃ PreProdNum.prune_assoc

end ProdNum
