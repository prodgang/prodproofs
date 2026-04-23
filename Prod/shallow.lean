import Prod.poset
-- Note: add `import Mathlib.Algebra.Squarefree.Basic` when proving shallow_iff_squarefree

/-!
## Shallow productive numbers

A list `xs : List RawProd` is **shallow** if every element is either `zero` or equivalent
to `nil = brak []`. This is the productive analogue of square-free natural numbers.

### Definition choice: recursive vs universal quantifier

Two equivalent options:

**Option A** (universal):
  `def shallow (xs : List RawProd) : Prop := ∀ x ∈ xs, x = zero ∨ ∃ ys, x = brak ys ∧ allzero ys`

**Option B** (recursive, used here):
  ```
  def shallow : List RawProd → Prop
    | []      => True
    | x :: xs => (x = zero ∨ ∃ ys, x = brak ys ∧ allzero ys) ∧ shallow xs
  ```

Option B is used because `shallow_cons_iff` is then definitional (no proof needed),
and induction proofs on lists get the case split built in. Option A may read more
naturally but requires a bridge lemma for every cons case.

To test which is better in practice: the key proof is `compl_raw_prune_equiv_nil`
in bool.lean, which does a pointwise case split. If that proof is awkward with B, switch to A.

### Main results
- `shallow_iff_pleq_nil`: bridge to the poset API
- `QProd.shallow_iff_squarefree`: correspondence with squarefree nats (deferred)
-/

namespace RawProd

-- ---------------------------------------------------------------------------
-- Section 1: Definition and basic API
-- ---------------------------------------------------------------------------



/-- `xs` is shallow if every element is either `zero` or `brak ys` for some allzero `ys`.
    Productive analogue of square-free natural numbers. -/
def shallow : List RawProd → Prop
  | []      => True
  | x :: xs => (x = zero ∨ ∃ ys, x = brak ys ∧ allzero ys) ∧ shallow xs

-- Definitional unfoldings (no proof needed with recursive definition)
-- @[simp] lemma shallow_nil_eq : shallow [] := rfl
-- @[simp] lemma shallow_cons_iff {x : RawProd} {xs : List RawProd} :
--     shallow (x :: xs) ↔ (x = zero ∨ ∃ ys, x = brak ys ∧ allzero ys) ∧ shallow xs := Iff.rfl
lemma shallow_nil : shallow [] := by simp only [shallow]

lemma shallow_cons_iff {x : RawProd} {xs : List RawProd} : shallow (x::xs) ↔ (x = zero ∨ ∃ ys, x = brak ys ∧ allzero ys) ∧ shallow xs := by
  simp only [shallow]


lemma allzero_shallow {xs : List RawProd} (hs : allzero xs) : shallow xs := by
  induction xs with
  | nil => simp only [shallow]
  | cons xh xt ih =>
    obtain ⟨h1, h2⟩ := allzero_cons hs
    simp only [shallow]
    constructor
    . left; exact h1
    . exact ih h2

-- lemma shallow_alt {xs : List RawProd} : shallow xs ↔ (∀ x ∈ xs, x = zero ∨  (∃ ys, x = brak ys ∧ allzero ys) ) := sorry

-- -- A non-shallow list has a concrete counterexample
-- lemma not_shallow_iff {xs : List RawProd} :
--     ¬shallow xs ↔ ∃ x ∈ xs, x ≠ zero ∧ ∀ ys, x = brak ys → ¬allzero ys := by sorry
-- -- induction using shallow_cons_iff; push negation

-- Bridge to the poset order (uses pleq_nil_cases from poset.lean)
lemma shallow_iff_pleq_nil {xs : List RawProd} :
    shallow xs ↔ ∀ i, get xs i ⊑ nil := by
      induction xs with
      | nil => constructor; intro h i; rw [get_nil]; exact zero_pleq; intro _; exact shallow_nil
      | cons xh xt ih =>
        simp only [shallow]
        constructor
        . intro hh i
          cases i with
          | zero => cases hh.1 with
            | inl h_head => rw [get_cons_zero, h_head]; exact zero_pleq
            | inr hys => obtain ⟨_, hys, haz⟩ := hys; rw [get_cons_zero, hys]; exact brak_pleq_nil_iff_allzero.mpr haz
          | succ j => rw [get_cons_succ]; exact ih.mp hh.2 j
        . intro h
          constructor
          · have h0 := h 0; rw [get_cons_zero] at h0; exact pleq_nil_cases h0
          · apply ih.mpr
            intro i
            have := h (i + 1)
            rwa [get_cons_succ] at this


-- Shallow is downward-closed under componentwise ⊑
lemma pleq_shallow {xs ys : List RawProd}
    (hs : shallow ys) (hle : brak xs ⊑ brak ys) : shallow xs := by
      induction xs generalizing ys with
      | nil => simp only [shallow]
      | cons xh xt ih =>
        cases ys with
        | nil => apply allzero_shallow; exact brak_pleq_nil_iff_allzero.mp hle
        | cons yh yt =>
          obtain ⟨h1, h2⟩ := cons_pleq_cons_iff.mp hle
          simp only [shallow] at ⊢ hs
          constructor
          . cases hs.1 with
            | inl hyz => left; rw [hyz] at h1; exact pleq_zero_eq_zero h1
            | inr hyaz =>
              obtain ⟨yhs, ⟨hyhs, hazys⟩⟩ := hyaz
              rw [hyhs] at h1
              apply pleq_nil_cases
              exact pleq_transitivity h1 (brak_pleq_nil_iff_allzero.mpr hazys)
          . exact ih hs.2 h2



-- ---------------------------------------------------------------------------
-- Section 2: Squarefree correspondence (deferred)
-- ---------------------------------------------------------------------------

-- DEFERRED: needs Mathlib.Algebra.Squarefree.Basic.
-- Strategy:
--   factorization_interp_list: (interp_raw (brak xs)).factorization (nth_prime i) = interp_raw (get xs i)
--   Squarefree n ↔ ∀ p prime, n.factorization p ≤ 1  (mathlib)
--   interp_raw x ≤ 1 ↔ x = zero ∨ (∃ ys, x = brak ys ∧ allzero ys)  (helper needed)
--   Combined: Squarefree (interp_raw (brak xs)) ↔ shallow xs
-- theorem shallow_iff_squarefree {xs : List RawProd} :
--     Squarefree (interp_raw (brak xs)) ↔ shallow xs := by sorry

end RawProd

-- ---------------------------------------------------------------------------
-- QProd section
-- ---------------------------------------------------------------------------

namespace QProd

open RawProd

/-- `x` is shallow if its representative list is shallow. False for QProd.zero
    (since zero.rep = RawProd.zero, which is not brak-form). -/
def shallow (x : QProd) : Prop :=
  match x.rep with
  | RawProd.zero    => False
  | RawProd.brak xs => RawProd.shallow xs

/-- A shallow `x` has representative `brak xs` for some shallow `xs`. -/
lemma shallow_exists_brak_rep {x : QProd} (hx : shallow x) :
    ∃ xs, x.rep = brak xs ∧ RawProd.shallow xs := by
  cases hrep : x.rep with
  | zero    => simp only [QProd.shallow, hrep] at hx
  | brak xs => exact ⟨xs, rfl, by rwa [QProd.shallow, hrep] at hx⟩


end QProd
