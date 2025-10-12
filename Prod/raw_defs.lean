import Mathlib.Data.List.Basic
import Mathlib.Tactic

/-- Raw productive numbers before quotient -/
inductive RawProd where
  | zero : RawProd
  | cons : List RawProd → RawProd
  deriving Repr

namespace RawProd

variable {P : RawProd → Prop}

/-- Decidable equality for RawProd -/
def beq : RawProd → RawProd → Bool
  | zero, zero => true
  | cons xs, cons ys => beqList xs ys
  | _, _ => false
where
  beqList : List RawProd → List RawProd → Bool
    | [], [] => true
    | x::xs, y::ys => beq x y && beqList xs ys
    | _, _ => false

instance : BEq RawProd where
  beq := beq


theorem beq_eq : ∀ (a b : RawProd), beq a b = true → a = b := by
  intro a b
  match a, b with
  | zero, zero => intro _; rfl
  | zero, cons _ => intro h; simp only [beq, Bool.false_eq_true] at h
  | cons _, zero => intro h; simp only [beq, Bool.false_eq_true] at h
  | cons xs, cons ys =>
    intro h
    simp only [beq] at h
    congr
    exact beqList_eq xs ys h
where
  beqList_eq : ∀ (xs ys : List RawProd), beq.beqList xs ys = true → xs = ys := by
    intro xs ys
    match xs, ys with
    | [], [] => intro _; rfl
    | [], _::_ => intro h; simp only [beq.beqList, Bool.false_eq_true] at h
    | _::_, [] => intro h; simp only [beq.beqList, Bool.false_eq_true] at h
    | x::xs, y::ys =>
      intro h
      simp only [beq.beqList, Bool.and_eq_true] at h
      obtain ⟨h1, h2⟩ := h
      congr
      · exact beq_eq x y h1
      · exact beqList_eq xs ys h2

theorem eq_beq : ∀ (a b : RawProd), a = b → beq a b = true := by
  intro a b heq
  rw [heq]
  match b with
  | zero => rfl
  | cons xs =>
    simp only [beq]
    exact eqList_beq xs
where
  eqList_beq : ∀ (xs : List RawProd), beq.beqList xs xs = true := by
    intro xs
    match xs with
    | [] => rfl
    | x::xs =>
      simp only [beq.beqList, Bool.and_eq_true]
      exact ⟨eq_beq x x rfl, eqList_beq xs⟩

instance : DecidableEq RawProd := fun a b =>
  if h : beq a b then
    isTrue (beq_eq a b h)
  else
    isFalse (fun heq => h (eq_beq a b heq))

lemma beq_rfl : ∀ x : RawProd, (beq x x) = true := by
  simp only [eq_beq, implies_true]


instance : LawfulBEq RawProd where
  rfl := @beq_rfl
  eq_of_beq := @beq_eq


/-- Induction principle for RawProd first -/
theorem induction {P : RawProd → Prop}
    (h_zero : P zero)
    (h_cons : ∀ xs : List RawProd, (∀ x ∈ xs, P x) → P (cons xs))
    (x : RawProd) : P x :=
  match x with
  | zero => h_zero
  | cons xs => h_cons xs (fun x _ => induction h_zero h_cons x)


theorem induction₂
 {P : RawProd → RawProd → Prop}
  (h_zero_left  : ∀ y,                 P zero      y)
  (h_zero_right : ∀ x,                 P x         zero)
  (h_cons_cons  : ∀ xs ys,
     (∀ x ∈ xs, ∀ y ∈ ys, P x y) →
     P (cons xs) (cons ys)) :
  ∀ x y, P x y := by
  intro x y
  -- outer induction on x, generalizing y so ih_x : ∀ x'∈xs, ∀ y, P x' y
  induction x using induction generalizing y with
  | h_zero      => exact h_zero_left y
  | h_cons xs ih_x =>
    -- inner induction on y; ih_x already speaks for ALL y
    induction y using induction with
    | h_zero      => exact h_zero_right (cons xs)
    | h_cons ys   =>
      apply h_cons_cons xs ys
      intro x' hx y' hy
      exact ih_x x' hx y'


/-- size measure used for termination. -/
def size : RawProd → Nat
| RawProd.zero => 0
| RawProd.cons xs => 1 + xs.foldl (fun acc r => acc + size r) 0


end RawProd
