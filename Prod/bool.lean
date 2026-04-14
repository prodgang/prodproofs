import Prod.shallow
import Prod.heyting
import Mathlib.Order.BooleanAlgebra.Defs

/-!
## Boolean algebra on non-zero principal downsets

Main theorem:
  `instance (x : QProd) (hx : QProd.shallow x) : BooleanAlgebra (QProd.NonZeroDownset x)`

where `NonZeroDownset x = {y : QProd | nil ≤ y ∧ y ≤ x}`, `nil = mk (brak [])`.

**Forward (shallow → BA)**: For shallow x, each y ≤ x has components in {zero, nil}.
Complement: compl(y)_i = x_i if y_i = zero, else zero.
Since x_i ∈ {zero, nil}, this is: nil if y_i = zero and x_i = nil; zero otherwise.
Then y ⊓ compl(y) ≡ nil (bottom) and y ⊔ compl(y) ≡ x (top).

**Backward (¬shallow → ¬BA)**: If x has some component x_j > nil, consider the element
e_j (= brak with nil in position j, zeros elsewhere). For any candidate complement c:
  - e_j ⊓ c = nil forces c_j = zero (nil ⊓ c_j = zero iff c_j = zero)
  - But then (e_j ⊔ c)_j = nil ≠ x_j, so e_j ⊔ c ≠ x. Contradiction.

**BooleanAlgebra constructor**: Use the explicit constructor (not `DistribLattice.booleanAlgebraOfComplemented`
which uses choice). More tedious but keeps the file constructive.

**REFACTOR NEEDED (Sections 1–2)**: Since zero is excluded from NonZeroDownset, the
complement API should be entirely List-based: `compl_list (xs ys : List RawProd) : List RawProd`
rather than `compl_raw : RawProd → RawProd → RawProd`. The `| _, _ => zero` fallback case
is never used. QProd-level proofs then pattern-match on `brak xs` form directly.
This refactor is deferred — marked with REFACTOR comments below.

TODO (deferred): isomorphism between NonZeroDownset x and the divisor boolean algebra
of a squarefree natural number.
-/

namespace RawProd

-- ---------------------------------------------------------------------------
-- Section 1: Complement definition and API
-- ---------------------------------------------------------------------------

/-- Pointwise complement of y within x. Component i: x_i if y_i = zero, else zero.
    Well-defined as a BA complement when shallow x and nil ⊑ y ⊑ x. -/
def compl_raw : RawProd → RawProd → RawProd
  | brak xs, brak ys => brak (List.zipWith (fun xi yi => if yi = zero then xi else zero) xs ys)
  | _,       _       => zero

-- Pointwise reduction (key lemma for all complement proofs)
lemma get_compl_raw (xs ys : List RawProd) (i : ℕ) :
    get (compl_raw (brak xs) (brak ys)) i =
    if get ys i = zero then get xs i else zero := by sorry
-- unfold compl_raw, induction on i/lists, use get_nil and get_cons

-- Complement is bounded above by x
lemma compl_raw_pleq {x y : RawProd} (hyx : y ⊑ x) : compl_raw x y ⊑ x := by sorry
-- componentwise: if y_i ≠ zero then compl_i = zero ⊑ x_i; if y_i = zero then compl_i = x_i ⊑ x_i

-- Complement is above nil when x is non-zero shallow and nil ⊑ y
-- REFACTOR: signature should take `(xs ys : List RawProd)` directly once compl becomes list-based.
lemma nil_pleq_compl_raw {x y : RawProd} (hyx : y ⊑ x) (hny : nil ⊑ y) : nil ⊑ compl_raw x y := by sorry
-- x = brak xs (non-zero from nil ⊑ y ⊑ x). y = brak ys. compl_raw = brak (...). nil_pleq_brak.

-- ---------------------------------------------------------------------------
-- Section 2: Boolean algebra axioms
-- ---------------------------------------------------------------------------

-- y ⊓ compl_raw x y ≡ nil (bottom)
-- REFACTOR: should take (xs ys : List RawProd) once compl is list-based.
-- Strategy: x = brak xs, y = brak ys. shallow xs → y_i ∈ {zero, nil}.
--   y_i = zero: y_i ⊓ x_i = zero (prune_zero).
--   y_i = nil:  compl_i = zero, nil ⊓ zero = zero.
-- All components zero → result ≡ nil.
lemma compl_raw_prune_equiv_nil {x y : RawProd} (hyx : y ⊑ x)
    (hny : nil ⊑ y) : (y ⊓ compl_raw x y).equiv nil := by sorry

-- y ⊔ compl_raw x y ≡ x (top)
-- REFACTOR: same as above.
-- Strategy: x = brak xs, y = brak ys. shallow xs → x_i ∈ {zero, nil}.
--   y_i = zero: zero ⊔ x_i = x_i.
--   y_i = nil:  compl_i = zero, nil ⊔ zero = nil = x_i.
-- All components match x_i → result ≡ x.
lemma compl_raw_graft_equiv_x {x y : RawProd} (hyx : y ⊑ x)
    (hny : nil ⊑ y) : (y ⊔ compl_raw x y).equiv x := by sorry

-- ---------------------------------------------------------------------------
-- Section 3: Backward direction — ¬shallow → no complement exists
-- ---------------------------------------------------------------------------

-- nil ⊓ c = zero iff c = zero (used to force c_j = zero from the prune condition)
lemma nil_prune_eq_zero_iff {c : RawProd} : nil ⊓ c = zero ↔ c = zero := by sorry
-- nil ⊓ zero = zero (prune_zero_eq_zero). nil ⊓ brak ys = brak [] ≠ zero (brak_prune_brak_neq_zero).

-- The element with nil in position j, zeros elsewhere
def singleton_j (j : ℕ) : RawProd := brak (List.replicate j zero ++ [nil])

-- singleton_j j ⊑ brak xs when nil ⊑ get xs j
lemma singleton_j_pleq {xs : List RawProd} (j : ℕ) (hj : nil ⊑ get xs j) :
    singleton_j j ⊑ brak xs := by sorry

-- Backward: for any j with get xs j > nil, no complement exists in NonZeroDownset (brak xs)
lemma not_shallow_no_complement {xs : List RawProd} (j : ℕ)
    (hj : ¬(get xs j ⊑ nil)) (hj' : nil ⊑ get xs j)
    (c : RawProd) (hc_prune : singleton_j j ⊓ c = nil) :
    singleton_j j ⊔ c ≠ brak xs := by sorry
-- From hc_prune: (nil ⊓ c_j) = (nil ⊓ get c_list j) — component j of nil is...
-- UNCERTAIN: getting component j of singleton_j ⊓ c requires careful use of get_compl_raw analog.
-- Core: nil_prune_eq_zero_iff forces c_j = zero, then (singleton_j ⊔ c)_j = nil ≠ get xs j.

end RawProd

-- ---------------------------------------------------------------------------
-- QProd section
-- ---------------------------------------------------------------------------

namespace QProd

open RawProd

/-- The complement of y within the NonZeroDownset of shallow x. -/
def complNZD (x : QProd) (hx : shallow x) (y : NonZeroDownset x) : NonZeroDownset x :=
  ⟨mk (compl_raw x.rep y.1.rep),
   ⟨by sorry,  -- nil ≤ compl: from nil_pleq_compl_raw (lifted to QProd)
    by sorry⟩⟩ -- compl ≤ x: from compl_raw_pleq (lifted to QProd)

/-- The non-zero principal downset: {y | nil ≤ y ≤ x}. -/
def nonZeroDownsetSublattice (x : QProd) : Sublattice QProd where
  carrier    := {y | nil ≤ y ∧ y ≤ x}
  supClosed' := fun _ ha _ hb =>
    ⟨le_trans ha.1 le_sup_left, sup_le ha.2 hb.2⟩
  infClosed' := fun _ ha _ hb =>
    ⟨by sorry,  -- nil ≤ y ⊓ z: both are brak-form so nil_pleq_brak applies
     inf_le_left.trans ha.2⟩

abbrev NonZeroDownset (x : QProd) : Type := ↥(nonZeroDownsetSublattice x)

instance (x : QProd) : Lattice (NonZeroDownset x) := inferInstance
instance (x : QProd) : DistribLattice (NonZeroDownset x) :=
  DistribLattice.ofInfSupLe fun a b c => by
    apply le_of_eq; apply Subtype.ext
    exact QProd.distrib a.val b.val c.val

instance (x : QProd) (hx : shallow x) : BoundedOrder (NonZeroDownset x) where
  top    := ⟨x, by sorry, le_refl x⟩  -- nil ≤ x when x is shallow (from shallow definition)
  le_top := fun a => a.2.2
  bot    := ⟨nil, le_refl nil, by sorry⟩  -- nil ≤ x when x is shallow
  bot_le := fun a => a.2.1

/-- NonZeroDownset x is a BooleanAlgebra when x is shallow.
    TODO: verify exact mathlib constructor — likely `BooleanAlgebra.ofCompl` or
    providing compl + inf_compl_le_bot + top_le_sup_compl. -/
instance (x : QProd) (hx : shallow x) : BooleanAlgebra (NonZeroDownset x) := by
  sorry
  -- provide complNZD x hx as the complement, then:
  -- inf_compl_le_bot: compl_raw_prune_equiv_nil lifted to QProd equality
  -- top_le_sup_compl: compl_raw_graft_equiv_x lifted to QProd equality

end QProd
