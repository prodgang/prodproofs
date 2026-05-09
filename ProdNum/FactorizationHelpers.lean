/-
Copyright (c) 2024 Prod Gang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prod Gang
-/
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.Nat.Nth
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Nat.Prime.Nth
import Mathlib.NumberTheory.PrimeCounting

/-!
# Factorization helpers

Miscellaneous lemmas about `Nat.factorization` and `Nat.nth Nat.Prime`
used throughout the productive-numbers library.
-/

lemma prime_index {p : ℕ} (hp : Nat.Prime p) : ∃ i, p = Nat.nth Nat.Prime i := by
  obtain ⟨i, hi⟩ := Nat.subset_range_nth hp
  exact ⟨i, hi.symm⟩

lemma prime_index_lt {i : ℕ} : i < Nat.nth Nat.Prime i := by
  have := Nat.add_two_le_nth_prime i; omega

lemma primes_distinct {n m : ℕ} (h : n ≠ m) : Nat.nth Nat.Prime n ≠ Nat.nth Nat.Prime m :=
  fun heq => h ((Nat.nth_strictMono Nat.infinite_setOf_prime).injective heq)

lemma factorization_add {p n m : ℕ} :
    (n.factorization + m.factorization) p = n.factorization p + m.factorization p := by
  simp only [Nat.factorization, Finsupp.coe_add, Finsupp.coe_mk, Pi.add_apply]

/-- If `n.factorization p ≠ 0` then `p ∣ n`. -/
lemma dvd_of_factorization_ne_zero {n p : ℕ} (h : n.factorization p ≠ 0) : p ∣ n := by
  by_contra hnd
  exact h ((Nat.factorization_eq_zero_iff n p).mpr (Or.inr (Or.inl hnd)))
