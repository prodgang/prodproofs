/-
Copyright (c) 2024 Edwin Agnew. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Edwin Agnew
-/
import Mathlib.Data.List.Basic
import Mathlib.Data.List.Induction

/-!
# Productive Numbers — Raw Definitions

Defines `RawProd`, the raw inductive type for productive numbers before taking the quotient.
A `RawProd` is either `zero` (representing 0) or `brak xs` where `xs : List RawProd`,
interpreted as `∏ pᵢ ^ eval(xᵢ)` where `pᵢ` is the `i`-th prime.

Trailing zeros in the list do not change the value, so equality is taken up to normalization
in `QProd` (defined in `Quot`).

## Main definitions

- `RawProd`: the raw inductive type
- `RawProd.get`: safe list accessor, defaulting to `zero`
- `RawProd.induction`, `induction_list`, `induction₂`, etc.: induction principles
- `DecidableEq RawProd`: via mutual structural recursion
-/

/-- Raw productive numbers before quotient -/
inductive RawProd where
  | zero : RawProd
  | brak : List RawProd → RawProd
  deriving Repr

namespace RawProd

/-- The minimum non-zero RawProd element. -/
abbrev nil : RawProd := brak []

@[simp]
lemma zero_ne_brak {xs : List RawProd} : zero ≠ brak xs := by simp only [ne_eq, reduceCtorEq, not_false_eq_true]

@[simp]
lemma brak_ne_zero {xs : List RawProd} : brak xs ≠ zero := by simp only [ne_eq, reduceCtorEq, not_false_eq_true]

/-- Access the i-th element of a list, defaulting to zero. -/
def get (xs : List RawProd) (i : ℕ) : RawProd := xs.getD i zero

@[simp] lemma get_nil {i : ℕ} : get [] i = zero := by
  simp only [get, List.getD_eq_getElem?_getD, List.length_nil, Nat.not_lt_zero, not_false_eq_true,
    getElem?_neg, Option.getD_none]

@[simp] lemma get_cons_zero {x : RawProd} {xs : List RawProd} : get (x :: xs) 0 = x := by
  simp only [get, List.getD_eq_getElem?_getD, List.length_cons, Nat.zero_lt_succ, getElem?_pos,
    List.getElem_cons_zero, Option.getD_some]

@[simp] lemma get_cons_succ {x : RawProd} {xs : List RawProd} {i : ℕ} : get (x :: xs) (i + 1) = get xs i := by
  simp only [get, List.getD_eq_getElem?_getD, List.getElem?_cons_succ]

lemma get_replicate_nil_pos (j : ℕ) :
    get (List.replicate j zero ++ [nil]) j = nil := by
  induction j with
  | zero => simp only [List.replicate_zero, List.nil_append, get_cons_zero]
  | succ n ih => simp only [List.replicate_succ, List.cons_append, get_cons_succ, ih]

-- Decidable equality via mutual structural recursion; BEq and LawfulBEq synthesize automatically.
mutual
  def decEqRaw : (a b : RawProd) → Decidable (a = b)
    | .zero,    .zero   => isTrue rfl
    | .zero,    .brak _ => isFalse (by simp only [zero_ne_brak, not_false_eq_true])
    | .brak _,  .zero   => isFalse (by simp only [brak_ne_zero, not_false_eq_true])
    | .brak xs, .brak ys =>
      match decEqList xs ys with
      | isTrue h  => isTrue (congrArg RawProd.brak h)
      | isFalse h => isFalse (by simp only [brak.injEq, h, not_false_eq_true])

  def decEqList : (as bs : List RawProd) → Decidable (as = bs)
    | [],    []    => isTrue rfl
    | [],    _::_  => isFalse (by simp only [List.nil_eq, reduceCtorEq, not_false_eq_true])
    | _::_,  []    => isFalse (by simp only [reduceCtorEq, not_false_eq_true])
    | a::as, b::bs =>
      match decEqRaw a b with
      | isFalse h => isFalse (by simp only [List.cons.injEq, h, false_and, not_false_eq_true])
      | isTrue ha =>
        match decEqList as bs with
        | isTrue hbs => isTrue (by rw [ha, hbs])
        | isFalse h  => isFalse (by simp only [List.cons.injEq, h, and_false, not_false_eq_true])
end

instance : DecidableEq RawProd := decEqRaw

/-- Induction principle for RawProd first -/
theorem induction {P : RawProd → Prop}
    (h_zero : P zero)
    (h_brak : ∀ xs : List RawProd, (∀ x ∈ xs, P x) → P (brak xs))
    (x : RawProd) : P x :=
  match x with
  | zero => h_zero
  | brak xs => h_brak xs (fun x _ => induction h_zero h_brak x)

theorem induction_list {P : RawProd → Prop}
    (h_zero : P zero)
    (h_nil : P nil)
    (h_cons : ∀ x xs, P x → P (brak xs) → P (brak (x::xs)))
    : ∀ x, P x := by
    intro x
    induction x using induction with
    | h_zero => exact h_zero
    | h_brak xs ih =>
      induction xs with
      | nil => exact h_nil
      | cons xh xs ihxs =>
        apply h_cons
        . apply ih; exact List.mem_cons_self
        . apply ihxs; intro x hx; apply ih; exact (List.mem_cons_of_mem xh hx)


theorem induction₂
 {P : RawProd → RawProd → Prop}
  (h_zero_left  : ∀ y,                 P zero      y)
  (h_zero_right : ∀ x,                 P x         zero)
  (h_brak_brak  : ∀ xs ys,
     (∀ x ∈ xs, ∀ y ∈ ys, P x y) →
     P (brak xs) (brak ys)) :
  ∀ x y, P x y := by
  intro x y
  -- outer induction on x, generalizing y so ih_x : ∀ x'∈xs, ∀ y, P x' y
  induction x using induction generalizing y with
  | h_zero      => exact h_zero_left y
  | h_brak xs ih_x =>
    -- inner induction on y; ih_x already speaks for ALL y
    induction y using induction with
    | h_zero      => exact h_zero_right (brak xs)
    | h_brak ys   =>
      apply h_brak_brak xs ys
      intro x' hx y' hy
      exact ih_x x' hx y'


theorem induction_list₂
 {P : RawProd → RawProd → Prop}
  (h_zero_left  : ∀ y,                 P zero      y)
  (h_zero_right : ∀ x,                 P x         zero)
  (h_nil_left   : ∀ ys,                P nil (brak ys))
  (h_nil_right  : ∀ xs,                P (brak xs) nil)
  (h_cons_cons  : ∀ x y xs ys,
     (P x y) →
     (P (brak xs) (brak ys)) →
     P (brak (x::xs)) (brak (y::ys)))
  : ∀ x y, P x y := by
    intro x y
    induction x using induction_list generalizing y with
    | h_zero => exact h_zero_left _
    | h_nil =>
      cases y
      . exact h_zero_right _
      . exact h_nil_left _
    | h_cons xh xts hx hxs =>
      cases y with
      | zero => exact h_zero_right _
      | brak ys =>
      cases ys with
        | nil => exact h_nil_right _
        | cons yh yts =>
          apply h_cons_cons
          . exact (hx _)
          . exact (hxs _)

theorem induction_list₃
 {P : RawProd → RawProd → RawProd → Prop}
  (h_zero_left  : ∀ y z, P zero y z)
  (h_zero_mid : ∀ x z, P x zero z)
  (h_zero_right : ∀ x y, P x y zero)
  (h_nil_left   : ∀ ys zs,                P nil (brak ys) (brak zs))
  (h_nil_mid   : ∀ xs zs,                 P (brak xs) nil (brak zs))
  (h_nil_right  : ∀ xs ys,                P (brak xs) (brak ys) nil)
  (h_cons_cons_cons  : ∀ x y z xs ys zs ,
    (P x y z) → (P (brak xs) (brak ys) (brak zs))
    → P (brak (x::xs)) (brak (y::ys)) (brak (z::zs)))
    : ∀ x y z, P x y z := by
    intro x y z
    induction x using induction_list generalizing y z with
    | h_zero => exact h_zero_left _ _
    | h_nil =>
      cases y
      . exact h_zero_mid _ _
      . cases z
        . exact h_zero_right _ _
        . exact h_nil_left _ _
    | h_cons x xs hx hxs =>
      cases y with
      | zero => exact h_zero_mid _ _
      | brak ys =>
        cases z with
        | zero => exact h_zero_right _ _
        | brak zs =>
          cases ys with
          | nil => exact h_nil_mid _ _
          | cons y ys =>
            cases zs with
            | nil => exact h_nil_right _ _
            | cons z zs =>
              apply h_cons_cons_cons
              . exact hx _ _
              . exact hxs _ _

theorem induction_list₄
 {P : RawProd → RawProd → RawProd → RawProd → Prop}
  (h_zero1  : ∀ x y z, P zero x y z)
  (h_zero2 : ∀ w y z, P w zero y z)
  (h_zero3 : ∀ w x z, P w x zero z)
  (h_zero4 : ∀ w x y, P w x y zero)
  (h_nil1   : ∀ xs ys zs,                P nil (brak xs) (brak ys) (brak zs))
  (h_nil2   : ∀ ws ys zs,                P (brak ws) nil (brak ys) (brak zs))
  (h_nil3   : ∀ ws xs zs,                P (brak ws) (brak xs) nil (brak zs))
  (h_nil4   : ∀ ws xs ys,                P (brak ws) (brak xs) (brak ys) nil)
  (h_cons_cons_cons_cons  : ∀ w x y z ws xs ys zs ,
    (P w x y z) → (P (brak ws) (brak xs) (brak ys) (brak zs))
    → P (brak (w::ws)) (brak (x::xs)) (brak (y::ys)) (brak (z::zs)))
    : ∀ w x y z, P w x y z := by
    intro w x y z
    induction w using induction_list generalizing x y z with
    | h_zero => exact h_zero1 _ _ _
    | h_nil =>
      cases x
      . exact h_zero2 _ _ _
      . cases y
        . exact h_zero3 _ _ _
        . cases z
          . exact h_zero4 _ _ _
          . exact h_nil1 _ _ _
    | h_cons x xs hx hxs =>
      cases x with
      | zero => exact h_zero2 _ _ _
      | brak xs =>
        cases y with
        | zero => exact h_zero3 _ _ _
        | brak ys =>
          cases z with
          | zero => exact h_zero4 _ _ _
          | brak zs =>
            cases xs with
            | nil => exact h_nil2 _ _ _
            | cons x xs =>
              cases ys with
              | nil => exact h_nil3 _ _ _
              | cons y ys =>
                cases zs with
                | nil => exact h_nil4 _ _ _
                | cons z zs =>
                  apply h_cons_cons_cons_cons
                  . exact hx _ _ _
                  . exact hxs _ _ _

end RawProd
