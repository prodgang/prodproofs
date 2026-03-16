import Mathlib.Data.Nat.Prime.Nth


-- couple of lemmas that really shouldnt be my responsibility

lemma prime_index {p : ℕ } (hp : Nat.Prime p) : ∃ i, p = Nat.nth Nat.Prime i := by
  sorry

lemma prime_index_lt {i : ℕ } : i < Nat.nth Nat.Prime i := by
  sorry



lemma primes_distinct {n m : ℕ } (h : n ≠ m) : Nat.nth Nat.Prime n ≠ Nat.nth Nat.Prime m := by
  sorry
