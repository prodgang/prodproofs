/-
Copyright (c) 2024 Prod Gang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prod Gang
-/
import ProdNum.PreProdDefs
import ProdNum.QuotDefs
import ProdNum.PruneBasic
import ProdNum.FactorizationHelpers
import Mathlib.Algebra.GroupWithZero.Basic
import Mathlib.Data.Nat.PrimeFin

/-!
# Productive Numbers — Interpretation

Defines the interpretation `interp : PreProdNum → ℕ` and its quotient version
`ProdNum.interp : ProdNum → ℕ`, along with the inverse `fromNat`.

The interpretation sends `brak xs` to `∏ pᵢ ^ interp(xs[i])` where `pᵢ` is
the `i`-th prime (zero-indexed).

## Main definitions

- `PreProdNum.interp`, `PreProdNum.interp_list`: mutually recursive interpretation
- `PreProdNum.fromNat`: inverse of interpretation
- `ProdNum.interp`, `ProdNum.fromNat`: quotient-level versions

## Main results

- `PreProdNum.factorization_interp_list`: the "bridge lemma" — the exponent of the `(k+i)`-th
  prime in `interp_list xs k` equals `interp (get xs i)`
- `PreProdNum.equiv_interp_eq`: equivalent `PreProdNum` values have the same interpretation
-/

namespace PreProdNum

mutual
noncomputable def interp: PreProdNum → ℕ
  | zero => 0
  | brak xs => interp_list xs 0

noncomputable def interp_list : List PreProdNum → ℕ → ℕ
  | [], _ => 1
  | x :: xs, i => (Nat.nth Nat.Prime i) ^ interp x * interp_list xs (i + 1)
end


@[simp]
lemma interp_zero : interp zero = 0 := by
  simp only [interp]


lemma interp_nil {i : ℕ } : interp_list [] i = 1 := by
  simp only [interp_list]


lemma interp_list_neq_zero {i : ℕ} (xs : List PreProdNum): interp_list xs i ≠ 0 := by
  induction xs generalizing i with
  | nil => simp only [interp_list, ne_eq, one_ne_zero, not_false_eq_true]
  | cons x xs ih =>
    simp only [interp_list]
    exact mul_ne_zero (pow_ne_zero _ (Nat.prime_nth_prime i).pos.ne') ih

lemma interp_eq_zero_eq_zero {x : PreProdNum} (hz : PreProdNum.interp x = 0) : x = PreProdNum.zero := by
  match x with
  | zero => simp only
  | brak xs => simp only [interp, interp_list_neq_zero] at hz



lemma interp_cons_coprime {xs : List PreProdNum } {i j: ℕ } (hlt : i < j) : ¬  (Nat.nth Nat.Prime i) ∣ interp_list xs j := by
  induction xs generalizing i j with
  | nil =>
    simp only [interp_nil]
    apply Nat.Prime.not_dvd_one
    exact (Nat.prime_nth_prime i)
  | cons x xs ih =>
    simp only [interp_list]
    intro h
    apply Nat.Prime.dvd_or_dvd at h
    . cases h
      . rename_i hpow
        apply (Nat.Prime.dvd_of_dvd_pow (Nat.prime_nth_prime i)) at hpow
        rw [Nat.prime_dvd_prime_iff_eq] at hpow
        . apply primes_distinct at hpow
          . exact hpow
          . linarith
        . exact (Nat.prime_nth_prime i)
        . exact (Nat.prime_nth_prime j)
      . have hlt2 : i < (j+1) := by linarith
        apply (ih hlt2)
        assumption
    . exact Nat.prime_nth_prime i




/-- Adding a single zero to the end doesn't change interpretation -/
lemma interp_list_append_zero (xs : List PreProdNum) (k : ℕ) :
    interp_list (xs ++ [zero]) k = interp_list xs k := by
  induction xs generalizing k with
  | nil =>
    simp only [List.nil_append, interp_list, interp]
    rw [pow_zero, one_mul]
  | cons x xs ih =>
    simp only [List.cons_append, interp_list]
    rw [ih]

/-- A list of all zeros has interpretation 1 -/
lemma interp_list_allzero_eq_one_iff {xs : List PreProdNum} {k : ℕ} : allzero xs ↔ interp_list xs k = 1 := by
  constructor
  . intro h
    induction xs generalizing k with
    | nil => simp only [interp_list]
    | cons x xs ih =>
      simp only [interp_list, allzero_iff] at ih h ⊢
      rw [h x List.mem_cons_self, interp, pow_zero, one_mul]
      exact ih fun y hy => h y (List.mem_cons_of_mem x hy)
  . intro h
    apply allzero_iff.mpr
    induction xs generalizing k with
    | nil => simp only [List.not_mem_nil, IsEmpty.forall_iff, implies_true]
    | cons xh ht ih =>
      simp only [interp_list, mul_eq_one] at h
      simp only [List.mem_cons, forall_eq_or_imp]
      constructor
      . have hk := (Nat.pow_eq_one.mp h.1)
        cases hk
        . rename_i hpk; have hk := Nat.prime_nth_prime k; rw [hpk] at hk; contradiction
        . rename_i hi; exact interp_eq_zero_eq_zero hi
      . apply ih h.2

lemma interp_equiv_nil_eq_one_iff {x : PreProdNum } : x.equiv nil ↔ interp x = 1 := by
  cases x with
  | zero => simp only [equiv, normalize_zero, equiv_zero_eq_zero, normalize_nil, zero_ne_brak, interp_zero, zero_ne_one]
  | brak xs =>
    rw [interp]
    exact Iff.trans brak_equiv_nil_iff_allzero interp_list_allzero_eq_one_iff




@[aesop safe]
lemma interp_list_eq_interp_list_trim {xs : List PreProdNum} {k : ℕ} :
   interp_list (trim xs) k = interp_list xs k := by
  induction xs using List.reverseRecOn with
  | nil => simp only [trim, List.rdropWhile_nil]
  | append_singleton ys y ih =>
    cases y
    case zero => simp only [trim_append_zero, interp_list_append_zero]; exact ih
    case brak => simp only [trim_append_brak_eq_self]




mutual
lemma interp_eq_norm_interp : ∀ (x : PreProdNum), interp (normalize x) = interp x
  | zero => by simp only [normalize, interp_zero]
  | brak xs => by
      simp only [normalize, interp]
      rw [interp_list_eq_interp_list_trim]
      exact interp_list_map_normalize xs 0

lemma interp_list_map_normalize : ∀ (xs : List PreProdNum) (k : ℕ),
    interp_list (List.map normalize xs) k = interp_list xs k
  | [], _ => by simp only [List.map_nil, interp_list]
  | x :: xs, k => by
      simp only [List.map_cons, interp_list]
      rw [interp_eq_norm_interp x]
      congr 1
      exact interp_list_map_normalize xs (k + 1)
end



theorem equiv_interp_eq {x y : PreProdNum }: equiv x y → interp x = interp y := by
  revert x y
  apply PreProdNum.induction₂
  case h_zero_left => intro y h; apply equiv_zero_eq_zero at h; subst h; rfl
  case h_zero_right => intro x h; apply zero_equiv_eq_zero at h; subst h; rfl
  case h_brak_brak =>
    intro xs ys h_interp h_equiv
    simp only [interp]
    simp only [equiv, normalize] at h_equiv
    have h1 : interp_list (trim (List.map normalize xs)) 0 =
              interp_list (trim (List.map normalize ys)) 0 := by simp_all only [brak.injEq]
    simp only [interp_list_eq_interp_list_trim] at h1
    rw [interp_list_map_normalize, interp_list_map_normalize] at h1
    exact h1





/-! ## Bridge Lemma: connecting interp_list to prime factorizations -/

/--
The "Bridge Lemma":
The exponent of the `(k + i)`-th prime in the interpretation of `xs`
is equal to the interpretation of the `i`-th element of `xs`.
-/
lemma factorization_interp_list {xs : List PreProdNum} (k i : ℕ) :
    (interp_list xs k).factorization (Nat.nth Nat.Prime (k + i)) = interp (get xs i) := by
  induction xs generalizing k i with
  | nil =>
    simp only [interp_nil, get_nil, interp_zero]
    rw [Nat.factorization_one]; rfl
  | cons x xs ih =>
    simp only [interp_list, get]
    cases i with
    | zero =>
      simp only [add_zero, List.getD_eq_getElem?_getD, List.length_cons, lt_add_iff_pos_left,
        add_pos_iff, zero_lt_one, or_true, getElem?_pos, List.getElem_cons_zero, Option.getD_some]
      rw [Nat.factorization_mul, Nat.factorization_pow]
      simp only [Nat.prime_nth_prime, Nat.Prime.factorization, Finsupp.smul_single, smul_eq_mul, mul_one, Finsupp.coe_add, Pi.add_apply, Finsupp.single_eq_same, Nat.add_eq_left]
      · rw [Nat.factorization_eq_zero_of_not_dvd]
        apply interp_cons_coprime
        exact Nat.lt_succ_self k
      · apply pow_ne_zero; apply Nat.Prime.ne_zero; apply Nat.prime_nth_prime
      · exact interp_list_neq_zero _
    | succ j =>
      simp only [List.getD_eq_getElem?_getD, List.getElem?_cons_succ]
      rw [Nat.add_comm j 1, ←Nat.add_assoc]
      rw [Nat.factorization_mul]
      · rw [factorization_add]
        have hz : (Nat.nth Nat.Prime k ^ x.interp).factorization (Nat.nth Nat.Prime (k + 1 + j)) = 0 := by
          rw [Nat.factorization_pow]
          simp only [Nat.prime_nth_prime, Nat.Prime.factorization, Finsupp.smul_single, smul_eq_mul, mul_one, Finsupp.single_apply, ite_eq_right_iff]
          intro h; absurd h; apply primes_distinct; linarith
        rw [hz, zero_add]
        specialize ih (k + 1) j
        simp only [get, List.getD_eq_getElem?_getD] at ih
        exact ih
      . apply pow_ne_zero; apply Nat.Prime.ne_zero; apply Nat.prime_nth_prime
      . exact interp_list_neq_zero _

/-- k=0 specialisation of the Bridge Lemma. -/
lemma factorization_interp_list_zero {xs : List PreProdNum} (i : ℕ) :
    (interp_list xs 0).factorization (Nat.nth Nat.Prime i) = interp (get xs i) := by
  have h := factorization_interp_list (xs := xs) 0 i; simp only [Nat.zero_add] at h; exact h


noncomputable def fromNat : Nat → PreProdNum
  | 0 => zero
  | 1 => nil
  | n@(Nat.succ _) =>
      let max_index := n -- crude but valid upper bound: p_i > i, so factorization is zero past index n

      have n_neq_0: n ≠ 0 := by grind only

      brak (List.map (λi => fromNat (n.factorization (Nat.nth Nat.Prime i))) (List.range max_index))
termination_by n => n
decreasing_by
  rename_i n2 h
  simp only [namedPattern, Nat.succ_eq_add_one]
  have h2 : n = n2 + 1 := by simp only [h, Nat.succ_eq_add_one]
  rw [← h2]
  exact Nat.factorization_lt (Nat.nth Nat.Prime i) n_neq_0




-- If the gcd of two interp_lists is 1, then at each index one element must be zero.
lemma gcd_one_imp_pointwise_zero {xs ys : List PreProdNum}
    (hgcd : Nat.gcd (interp_list xs 0) (interp_list ys 0) = 1)
    (i : ℕ) : get xs i = zero ∨ get ys i = zero := by
  by_contra h
  simp only [not_or] at h
  obtain ⟨hx, hy⟩ := h
  have dvd_of : ∀ zs, get zs i ≠ zero → Nat.nth Nat.Prime i ∣ interp_list zs 0 := fun zs hn =>
    dvd_of_factorization_ne_zero (factorization_interp_list_zero i ▸ fun h => hn (interp_eq_zero_eq_zero h))
  exact absurd (hgcd ▸ Nat.dvd_gcd (dvd_of xs hx) (dvd_of ys hy))
    (Nat.Prime.not_dvd_one (Nat.prime_nth_prime i))

theorem prune_equiv_nil_iff_gcd_one {x y : PreProdNum} :
    (x ⊓ y).equiv nil ↔ x ≠ zero ∧ y ≠ zero ∧ Nat.gcd (interp x) (interp y) = 1 := by
  constructor
  · revert x y
    apply induction_list₂
    case h_zero_left => intro y h; rw [zero_prune] at h; absurd equiv_zero_eq_zero h; exact brak_ne_zero
    case h_zero_right => intro y h; rw [prune_zero] at h; absurd equiv_zero_eq_zero h; exact brak_ne_zero
    case h_nil_left => intro ys h; simp only [interp, interp_nil, Nat.gcd_one_left, and_true]; exact ⟨brak_ne_zero, brak_ne_zero⟩
    case h_nil_right => intro xs h; simp only [interp, interp_nil, Nat.gcd_one_right, and_true]; exact ⟨brak_ne_zero, brak_ne_zero⟩
    case h_cons_cons =>
      intro x y xs ys ih hs hnil
      refine ⟨brak_ne_zero, brak_ne_zero, ?_⟩
      simp only [interp, Nat.gcd_eq_one_iff]; intro c hcx hcy
      rw [prune] at hnil
      have haz := brak_equiv_nil_iff_allzero.mp hnil
      rw [prune_list_allzero_iff] at haz
      have hcnz : c ≠ 0 := by intro hc; rw [hc, Nat.zero_dvd] at hcx; exact interp_list_neq_zero (x :: xs) hcx
      apply (Nat.factorization_prime_le_iff_dvd hcnz (interp_list_neq_zero (x::xs))).mpr at hcx
      apply (Nat.factorization_prime_le_iff_dvd hcnz (interp_list_neq_zero (y::ys))).mpr at hcy
      suffices hz : ∀ p, Nat.Prime p → c.factorization p = 0 by
        apply Nat.eq_of_factorization_eq; exact hcnz; omega
        intro p; rw [Nat.factorization_one]
        by_cases hp : Nat.Prime p; apply hz p hp; apply Nat.factorization_eq_zero_of_not_prime c hp
      intro p hp
      obtain ⟨i, hi⟩ := prime_index hp
      specialize hcx p; specialize hcy p
      rw [hi] at hcx hcy
      rw [factorization_interp_list_zero] at hcx hcy
      cases haz i with
      | inl h => simp only [Nat.prime_nth_prime, h, interp_zero, nonpos_iff_eq_zero, forall_const] at hcx; simp only [hi, hcx]
      | inr h => simp only [Nat.prime_nth_prime, h, interp_zero, nonpos_iff_eq_zero, forall_const] at hcy; simp only [hi, hcy]


  . revert x y
    apply induction_list₂

    case h_zero_left => intro y h; absurd h.1; rfl
    case h_zero_right => intro x h; absurd h.2.1; rfl
    case h_nil_left => intro xs h; rw [nil_prune_brak_eq_nil]; exact equiv_refl nil
    case h_nil_right => intro ys h; rw [brak_prune_nil_eq_nil]; rfl
    case h_cons_cons =>
      intro x y xs ys ih hs hnil
      rw [prune, prune_list, brak_equiv_nil_iff_allzero, ← prune_list_cons, prune_list_allzero_iff]
      intro i
      apply gcd_one_imp_pointwise_zero
      simpa only [interp] using hnil.2.2



end PreProdNum

namespace ProdNum

/-- The interpretation function on quotient productive numbers -/
noncomputable def interp : ProdNum → ℕ :=
  Quotient.lift PreProdNum.interp @PreProdNum.equiv_interp_eq


/-! ## ProdNum interpretation -/

lemma interp_mk (x : PreProdNum) : interp (mk x) = PreProdNum.interp x := by
  simp only [interp, mk, Quotient.lift_mk]


noncomputable def fromNat (n : ℕ ) := mk (PreProdNum.fromNat n)

@[simp] lemma interp_zero : interp zero = 0 := rfl

@[simp] lemma interp_nil : interp (ofList []) = 1 := by
  simp only [interp, ofList, List.map_nil]
  apply Quotient.lift_mk



lemma fromNat_zero : fromNat 0 = zero := by
  simp only [fromNat, PreProdNum.fromNat, mk_zero_eq_zero]


lemma fromNat_one : fromNat 1 = ofList []  := by
  simp only [fromNat, PreProdNum.fromNat, mk_nil_eq_nil]

lemma interp_eq_zero_eq_zero {x : ProdNum} (hz : interp x = 0) : x = zero := by
  induction x using Quotient.ind
  rename_i a
  exact mk_zero_eq_zero ▸ congrArg mk (PreProdNum.interp_eq_zero_eq_zero hz)

end ProdNum
