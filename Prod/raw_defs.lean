import Mathlib.Data.List.Basic
import Mathlib.Tactic

/-- Raw productive numbers before quotient -/
inductive RawProd where
  | zero : RawProd
  | brak : List RawProd → RawProd
  deriving Repr

namespace RawProd

-- the most basic lemmas
@[aesop unsafe]
lemma zero_neq_brak (xs : List RawProd) : zero ≠ brak xs := by simp only [ne_eq, reduceCtorEq, not_false_eq_true]

@[aesop unsafe]
lemma brak_neq_zero (xs : List RawProd) : brak xs ≠ zero := by simp only [ne_eq, reduceCtorEq, not_false_eq_true]


variable {P : RawProd → Prop}

/-- Decidable equality for RawProd -/
def beq : RawProd → RawProd → Bool
  | zero, zero => true
  | brak xs, brak ys => beqList xs ys
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
  | zero, brak _ => intro h; simp only [beq, Bool.false_eq_true] at h
  | brak _, zero => intro h; simp only [beq, Bool.false_eq_true] at h
  | brak xs, brak ys =>
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
  | brak xs =>
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

/-- size measure used for termination. -/
def size : RawProd → Nat
| RawProd.zero => 0
| RawProd.brak xs => 1 + xs.foldl (fun acc r => acc + size r) 0



/-- Induction principle for RawProd first -/
theorem induction {P : RawProd → Prop}
    (h_zero : P zero)
    (h_brak : ∀ xs : List RawProd, (∀ x ∈ xs, P x) → P (brak xs))
    (x : RawProd) : P x :=
  match x with
  | zero => h_zero
  | brak xs => h_brak xs (fun x _ => induction h_zero h_brak x)


theorem strong_induction₂
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



theorem strong_induction₃
 {P : RawProd → RawProd → RawProd → Prop}
  (h_zero_left  : ∀ y z, P zero y z)
  (h_zero_mid : ∀ x z, P x zero z)
  (h_zero_right : ∀ x y, P x y zero)
  (h_brak_brak_brak  : ∀ xs ys zs ,
     (∀ x ∈ xs, ∀ y ∈ ys, ∀ z ∈ zs, P x y z) →
     P (brak xs) (brak ys) (brak zs)) :
  ∀ x y z, P x y z := by
  intro x y z
  -- outer induction on x, generalizing y so ih_x : ∀ x'∈xs, ∀ y, P x' y
  induction x using induction generalizing y z with
  | h_zero      => exact h_zero_left y z
  | h_brak xs ih_x =>
    -- inner induction on y; ih_x already speaks for ALL y
    induction y using induction generalizing z with
    | h_zero      => exact h_zero_mid (brak xs) z
    | h_brak ys ih_y  =>
      induction z using induction with
      | h_zero => exact h_zero_right (brak xs) (brak ys)
      | h_brak zs ih_z =>
        apply h_brak_brak_brak xs ys zs
        intro x' hx y' hy z' hz
        exact ih_x x' hx y' z'


@[simp]
def padPairF {α : Type _} (f : RawProd → RawProd → α) : List RawProd → List RawProd → List α
  | xs, ys => xs.zipWithAll (fun oa ob => (f (oa.getD zero) (ob.getD zero))) ys

/- takes two lists and creates a list of pairs, padding shorter list with zeros-/
def padPair : List RawProd → List RawProd → List (RawProd × RawProd)
  | xs, ys => padPairF (fun x y => (x,y)) xs ys




@[simp]
lemma padPair_nil (xs : List RawProd) : padPair xs [] = List.zip xs (List.replicate xs.length zero) := by
  simp only [padPair, padPairF, List.zipWithAll_nil, Option.getD_some, Option.getD_none]
  induction xs with
  | nil => simp only [List.map_nil, List.length_nil, List.replicate_zero, List.zip_nil_right]
  | cons x xx ih =>
    simp only [List.map_cons, List.length_cons]
    rw [List.replicate_succ]
    simp only [List.zip_cons_cons, List.cons.injEq, true_and]
    exact ih

@[simp]
lemma nil_padPair (xs : List RawProd) : padPair [] xs = List.zip (List.replicate xs.length zero) xs := by
  simp only [padPair, padPairF, List.nil_zipWithAll, Option.getD_none, Option.getD_some]
  induction xs with
  | nil => simp only [List.map_nil, List.length_nil, List.replicate_zero, List.zip_nil_right]
  | cons x xx ih =>
    simp only [List.map_cons, List.length_cons]
    rw [List.replicate_succ]
    simp only [List.zip_cons_cons, List.cons.injEq, true_and]
    exact ih



@[aesop unsafe]
lemma padPair_cases (x y : RawProd) (xs ys : List RawProd) : (x, y) ∈ padPair xs ys → (x,y) ∈ List.zip xs ys ∨ x = zero ∨ y = zero := by
  intro hxy
  --simp_all [zipPairs]
  induction xs generalizing ys with
  | nil =>
    simp only [nil_padPair] at hxy
    apply List.of_mem_zip at hxy
    simp only [List.mem_replicate, ne_eq, List.length_eq_zero_iff] at hxy
    simp_all only [List.zip_nil_left, List.not_mem_nil, true_or, or_true]
  | cons x' xx ihxx =>
      cases ys with
      | nil =>
        rw [padPair_nil] at hxy
        apply List.of_mem_zip at hxy
        simp only [List.mem_replicate, ne_eq, List.length_eq_zero_iff] at hxy
        simp only [List.zip_nil_right, hxy.right.right, List.not_mem_nil, or_true]
      | cons y' yy =>
          --apply ihxx yy hxy
          simp [padPair, padPairF] at hxy ihxx
          simp_all only [List.zip_cons_cons, List.mem_cons, Prod.mk.injEq]
          --left
          cases hxy with
          | inl h => simp_all only [and_self, true_or]
          | inr h_1 => sorry --simp [ihxx]

  -- waht i want is (x,y) in zipPairs -> (x,y) in zip or x = zero or y = zero


theorem induction₂ -- do i even need this??
 {P : RawProd → RawProd → Prop}
  (h_zero_left  : ∀ y, P zero y)
  (h_zero_right : ∀ x, P x zero)
  (h_brak_brak  : ∀ xs ys, (∀ p ∈ padPair xs ys, P p.1 p.2) → P (brak xs) (brak ys)) :
  ∀ x y, P x y := by
  intro x y
  induction x using RawProd.induction with
  | h_zero => exact h_zero_left y
  | h_brak xs ihx =>
    induction y using RawProd.induction with
    | h_zero => exact h_zero_right (brak xs)
    | h_brak ys ihy =>
        sorry
        -- P : RawProd → RawProd → Prop
        -- h_zero_left : ∀ (y : RawProd), P zero y
        -- h_zero_right : ∀ (x : RawProd), P x zero
        -- h_brak_brak : ∀ (xs ys : List RawProd), (∀ p ∈ zipPairs xs ys, P p.1 p.2) → P (brak xs) (brak ys)
        -- xs ys : List RawProd
        -- ihy : ∀ x ∈ ys, (∀ x_1 ∈ xs, P x_1 x) → P (brak xs) x
        -- ihx : ∀ x ∈ xs, P x (brak ys)
        -- ⊢ P (brak xs) (brak ys)
        -- this is bad because I want a pairwise ih....




end RawProd
