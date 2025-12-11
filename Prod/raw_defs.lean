import Mathlib.Data.List.Basic
import Mathlib.Data.List.Induction
-- import Mathlib.Tactic

/-- Raw productive numbers before quotient -/
inductive RawProd where
  | zero : RawProd
  | brak : List RawProd → RawProd
  deriving Repr

namespace RawProd

-- the most basic lemmas
@[simp]
lemma zero_neq_brak {xs : List RawProd} : zero ≠ brak xs := by simp only [ne_eq, reduceCtorEq, not_false_eq_true]

@[simp]
lemma brak_neq_zero {xs : List RawProd} : brak xs ≠ zero := by simp only [ne_eq, reduceCtorEq, not_false_eq_true]


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

theorem induction_list {P : RawProd → Prop}
    (h_zero : P zero)
    (h_nil : P (brak []))
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

theorem induction_reverse {P : RawProd → Prop}
    (h_zero : P zero)
    (h_nil : P (brak []))
    (h_append : ∀ xs x, P x → P (brak xs) → P (brak (xs ++ [x])))
    : ∀ x, P x := by
    intro x
    induction x using induction with
    | h_zero => exact h_zero
    | h_brak xs ih =>
      induction xs using List.reverseRecOn with
      | nil => exact h_nil
      | append_singleton xs xt ihxs =>
        apply h_append
        . apply ih; simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false, or_true]
        . apply ihxs; intro x hx; apply ih; exact List.mem_append_left [xt] hx


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


-- basically same as above but saves me typing out the list inductions each time and remembering what to generalize
-- theorem strong_list_induction₂
--  {P : RawProd → RawProd → Prop}
--   (h_zero_left  : ∀ y,                 P zero      y)
--   (h_zero_right : ∀ x,                 P x         zero)
--   (h_nil_left   : ∀ ys,                P (brak []) (brak ys))
--   (h_nil_right  : ∀ xs,                P (brak xs) (brak []))
--   (h_cons_cons  : ∀ x y xs ys,
--      (P x y) →
--      (P (brak xs) (brak ys)) →
--      P (brak (x::xs)) (brak (y::ys)))
--   : ∀ x y, P x y := by
--     apply RawProd.strong_induction₂
--     case h_zero_left => exact h_zero_left
--     case h_zero_right => exact h_zero_right
--     case h_brak_brak =>
--       intro xs ys ih
--       induction xs generalizing ys with
--       | nil => exact h_nil_left ys
--       | cons xh xts ihx =>
--         cases ys with
--         | nil => exact h_nil_right (xh::xts)
--         | cons yh yts =>
--           apply h_cons_cons
--           . simp only [List.mem_cons, true_or, ih]
--           . simp only [List.mem_cons] at ih --ihy
--             simp_all only [or_true, implies_true]


theorem induction_list₂
 {P : RawProd → RawProd → Prop}
  (h_zero_left  : ∀ y,                 P zero      y)
  (h_zero_right : ∀ x,                 P x         zero)
  (h_nil_left   : ∀ ys,                P (brak []) (brak ys))
  (h_nil_right  : ∀ xs,                P (brak xs) (brak []))
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


-- theorem strong_induction₃
--  {P : RawProd → RawProd → RawProd → Prop}
--   (h_zero_left  : ∀ y z, P zero y z)
--   (h_zero_mid : ∀ x z, P x zero z)
--   (h_zero_right : ∀ x y, P x y zero)
--   (h_brak_brak_brak  : ∀ xs ys zs ,
--      (∀ x ∈ xs, ∀ y ∈ ys, ∀ z ∈ zs, P x y z) →
--      P (brak xs) (brak ys) (brak zs)) :
--   ∀ x y z, P x y z := by
--   intro x y z
--   -- outer induction on x, generalizing y so ih_x : ∀ x'∈xs, ∀ y, P x' y
--   induction x using induction generalizing y z with
--   | h_zero      => exact h_zero_left y z
--   | h_brak xs ih_x =>
--     -- inner induction on y; ih_x already speaks for ALL y
--     induction y using induction generalizing z with
--     | h_zero      => exact h_zero_mid (brak xs) z
--     | h_brak ys ih_y  =>
--       induction z using induction with
--       | h_zero => exact h_zero_right (brak xs) (brak ys)
--       | h_brak zs ih_z =>
--         apply h_brak_brak_brak xs ys zs
--         intro x' hx y' hy z' hz
--         exact ih_x x' hx y' z'

-- tedious but easy
theorem induction_list₃
 {P : RawProd → RawProd → RawProd → Prop}
  (h_zero_left  : ∀ y z, P zero y z)
  (h_zero_mid : ∀ x z, P x zero z)
  (h_zero_right : ∀ x y, P x y zero)
  (h_nil_left   : ∀ ys zs,                P (brak []) (brak ys) (brak zs))
  (h_nil_mid   : ∀ xs zs,                 P (brak xs) (brak []) (brak zs))
  (h_nil_right  : ∀ xs ys,                P (brak xs) (brak ys) (brak []))
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

-- useful for lifting binary ops
theorem induction_list₄
 {P : RawProd → RawProd → RawProd → RawProd → Prop}
  (h_zero1  : ∀ x y z, P zero x y z)
  (h_zero2 : ∀ w y z, P w zero y z)
  (h_zero3 : ∀ w x z, P w x zero z)
  (h_zero4 : ∀ w x y, P w x y zero)
  (h_nil1   : ∀ xs ys zs,                P (brak []) (brak xs) (brak ys) (brak zs))
  (h_nil2   : ∀ ws ys zs,                P (brak ws) (brak []) (brak ys) (brak zs))
  (h_nil3   : ∀ ws xs zs,                P (brak ws) (brak xs) (brak []) (brak zs))
  (h_nil4   : ∀ ws xs ys,                P (brak ws) (brak xs) (brak ys) (brak []))
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


--@[simp]
def padWith {α : Type _} (f : RawProd → RawProd → α) : List RawProd → List RawProd → List α
  | xs, ys => xs.zipWithAll (fun oa ob => (f (oa.getD zero) (ob.getD zero))) ys

/- takes two lists and creates a list of pairs, padding shorter list with zeros-/
def pad : List RawProd → List RawProd → List (RawProd × RawProd)
  | xs, ys => padWith (fun x y => (x,y)) xs ys


lemma pad_nil (xs : List RawProd) : pad xs [] = List.zip xs (List.replicate xs.length zero) := by
  simp only [pad, padWith, List.zipWithAll_nil, Option.getD_some, Option.getD_none]
  induction xs with
  | nil => simp only [List.map_nil, List.length_nil, List.replicate_zero, List.zip_nil_right]
  | cons x xx ih =>
    simp only [List.map_cons, List.length_cons]
    rw [List.replicate_succ]
    simp only [List.zip_cons_cons, List.cons.injEq, true_and]
    exact ih


lemma nil_pad (xs : List RawProd) : pad [] xs = List.zip (List.replicate xs.length zero) xs := by
  simp only [pad, padWith, List.nil_zipWithAll, Option.getD_none, Option.getD_some]
  induction xs with
  | nil => simp only [List.map_nil, List.length_nil, List.replicate_zero, List.zip_nil_right]
  | cons x xx ih =>
    simp only [List.map_cons, List.length_cons]
    rw [List.replicate_succ]
    simp only [List.zip_cons_cons, List.cons.injEq, true_and]
    exact ih


lemma pad_cases_strong {p : RawProd × RawProd} {xs ys : List RawProd} (hxy : p ∈ pad xs ys ) :  p ∈ List.zip xs ys ∨ (p.1 = zero ∧ p.2 ∈ ys) ∨ (p.1 ∈ xs ∧ p.2 = zero) := by
induction xs generalizing ys with
  | nil =>
    simp only [nil_pad] at hxy
    apply List.of_mem_zip at hxy
    simp only [List.mem_replicate, ne_eq, List.length_eq_zero_iff] at hxy
    simp_all only [List.zip_nil_left, List.not_mem_nil, and_self, false_and, or_false, or_true]
  | cons x' xx ihxx =>
      cases ys with
      | nil =>
        rw [pad_nil] at hxy
        apply List.of_mem_zip at hxy
        simp only [List.mem_replicate, ne_eq, List.length_eq_zero_iff] at hxy
        simp only [List.zip_nil_right, List.not_mem_nil, hxy.right.right, and_false, List.mem_cons,
          and_true, false_or]
        rw [← List.mem_cons]
        exact hxy.left

      | cons y' yy =>
          --apply ihxx yy hxy
          simp only [pad, padWith, List.zipWithAll_cons_cons, Option.getD_some, List.mem_cons] at hxy ihxx
          simp_all only [List.zip_cons_cons, List.mem_cons]
          --left
          cases hxy with
          | inl h => simp_all only [true_or]
          | inr h_1 =>
            cases (ihxx h_1) with
            | inl l => left; right; exact l
            | inr r =>
                    right
                    obtain ⟨fst, snd⟩ := p
                    simp_all only
                    cases r with
                    | inl h => simp_all only [true_and, or_true, and_self, true_or]
                    | inr h_2 => simp_all only [and_self, or_true, implies_true]

-- lemma pad_cases {p : RawProd × RawProd} {xs ys : List RawProd} (hxy : p ∈ pad xs ys ) :  p ∈ List.zip xs ys ∨ p.1 = zero ∨ p.2 = zero := by
--   --intro hxy
--   --simp_all [zipPairs]
--   induction xs generalizing ys with
--   | nil =>
--     simp only [nil_pad] at hxy
--     apply List.of_mem_zip at hxy
--     simp only [List.mem_replicate, ne_eq, List.length_eq_zero_iff] at hxy
--     simp_all only [List.zip_nil_left, List.not_mem_nil, true_or, or_true]
--   | cons x' xx ihxx =>
--       cases ys with
--       | nil =>
--         rw [pad_nil] at hxy
--         apply List.of_mem_zip at hxy
--         simp only [List.mem_replicate, ne_eq, List.length_eq_zero_iff] at hxy
--         simp only [List.zip_nil_right, hxy.right.right, List.not_mem_nil, or_true]
--       | cons y' yy =>
--           --apply ihxx yy hxy
--           simp only [pad, padWith, List.zipWithAll_cons_cons, Option.getD_some, List.mem_cons] at hxy ihxx
--           simp_all only [List.zip_cons_cons, List.mem_cons]
--           --left
--           cases hxy with
--           | inl h => simp_all only [true_or]
--           | inr h_1 =>
--             cases (ihxx h_1) with
--             | inl l => left; right; exact l
--             | inr r => right; exact r


--@[simp]
 lemma pad_nil_cons (x : RawProd) (xs : List RawProd) : pad [] (x::xs) = (zero, x) :: pad [] xs := by
  simp only [nil_pad, List.length_cons, List.replicate_succ, List.zip_cons_cons]

--@[simp]
lemma pad_cons_nil (x : RawProd) (xs : List RawProd) : pad (x::xs) [] = (x, zero) :: pad xs [] := by
  simp only [pad_nil, List.length_cons, List.replicate_succ, List.zip_cons_cons]


--@[simp]
 lemma pad_cons_cons (x y : RawProd) (xs ys : List RawProd) : pad (x::xs) (y::ys) = (x,y) :: (pad xs ys) := by
  simp only [pad, padWith, List.zipWithAll_cons_cons, Option.getD_some]





-- theorem induction₂ -- pairwise not strong, do i even need this??
--  {P : RawProd → RawProd → Prop}
--   (h_zero_left  : ∀ y, P zero y)
--   (h_zero_right : ∀ x, P x zero)
--   (h_brak_brak  : ∀ xs ys, (∀ p ∈ padPair xs ys, P p.1 p.2) → P (brak xs) (brak ys)) :
--   ∀ x y, P x y := by
--   intro x y
--   induction x using RawProd.induction with
--   | h_zero => exact h_zero_left y
--   | h_brak xs ihx =>
--     induction y using RawProd.induction with
--     | h_zero => exact h_zero_right (brak xs)
--     | h_brak ys ihy =>
--         sorry
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
