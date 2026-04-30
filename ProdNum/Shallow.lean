/-
Copyright (c) 2024 Edwin Agnew. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Edwin Agnew
-/
import ProdNum.Poset

/-!
# Productive Numbers — Shallow Elements

A list `xs : List PreProdNum` is **shallow** if every element is either `zero` or equivalent
to `nil = brak []`. This is the productive analogue of square-free natural numbers.

## Main definitions

- `PreProdNum.shallow`: predicate on lists
- `ProdNum.shallow`: predicate on `ProdNum` (via representative)

## Main results

- `shallow_iff_pleq_nil`: `shallow xs ↔ ∀ i, get xs i ⊑ nil`
- `pleq_shallow`: shallowness is downward closed
-/

namespace PreProdNum

def shallow : List PreProdNum → Prop
  | []      => True
  | x :: xs => (x = zero ∨ ∃ ys, x = brak ys ∧ allzero ys) ∧ shallow xs

lemma shallow_nil : shallow [] := by simp only [shallow]

lemma shallow_cons_iff {x : PreProdNum} {xs : List PreProdNum} : shallow (x::xs) ↔ (x = zero ∨ ∃ ys, x = brak ys ∧ allzero ys) ∧ shallow xs := by
  simp only [shallow]


lemma shallow_iff_pleq_nil {xs : List PreProdNum} :
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


lemma pleq_shallow {xs ys : List PreProdNum}
    (hs : shallow ys) (hle : brak xs ⊑ brak ys) : shallow xs :=
  shallow_iff_pleq_nil.mpr fun i =>
    pleq_transitivity (brak_pleq_brak_get hle i) (shallow_iff_pleq_nil.mp hs i)



end PreProdNum

namespace ProdNum

/-- `x` is shallow if its representative list is shallow. False for ProdNum.zero
    (since zero.rep = PreProdNum.zero, which is not brak-form). -/
def shallow (x : ProdNum) : Prop :=
  match x.rep with
  | PreProdNum.zero    => False
  | PreProdNum.brak xs => PreProdNum.shallow xs

/-- A shallow `x` has representative `brak xs` for some shallow `xs`. -/
lemma shallow_exists_brak_rep {x : ProdNum} (hx : shallow x) :
    ∃ xs, x.rep = PreProdNum.brak xs ∧ PreProdNum.shallow xs := by
  cases hrep : x.rep with
  | zero    => simp only [ProdNum.shallow, hrep] at hx
  | brak xs => exact ⟨xs, rfl, by rwa [ProdNum.shallow, hrep] at hx⟩


end ProdNum
