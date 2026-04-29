/-
Copyright (c) 2024 Edwin Agnew. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Edwin Agnew
-/
import ProdNum.Poset

/-!
# Productive Numbers — Shallow Elements

A list `xs : List RawProd` is **shallow** if every element is either `zero` or equivalent
to `nil = brak []`. This is the productive analogue of square-free natural numbers.

## Main definitions

- `RawProd.shallow`: predicate on lists
- `QProd.shallow`: predicate on `QProd` (via representative)

## Main results

- `shallow_iff_pleq_nil`: `shallow xs ↔ ∀ i, get xs i ⊑ nil`
- `pleq_shallow`: shallowness is downward closed
-/

namespace RawProd

def shallow : List RawProd → Prop
  | []      => True
  | x :: xs => (x = zero ∨ ∃ ys, x = brak ys ∧ allzero ys) ∧ shallow xs

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


lemma pleq_shallow {xs ys : List RawProd}
    (hs : shallow ys) (hle : brak xs ⊑ brak ys) : shallow xs :=
  shallow_iff_pleq_nil.mpr fun i =>
    pleq_transitivity (brak_pleq_brak_get hle i) (shallow_iff_pleq_nil.mp hs i)



end RawProd

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
