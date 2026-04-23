import Prod.raw_defs
import Prod.quot_defs
import Prod.misc
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Nat.Nth
import Mathlib.Algebra.GroupWithZero.Basic
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.Nat.Prime.Nth
import Mathlib.NumberTheory.PrimeCounting

namespace RawProd

/-! ## Basic lemmas about trailing zeros -/


mutual
noncomputable def interp_raw: RawProd → ℕ
  | zero => 0
  | brak xs => interp_list xs 0

noncomputable def interp_list : List RawProd → ℕ → ℕ
  | [], _ => 1
  | x :: xs, i => (Nat.nth Nat.Prime i) ^ interp_raw x * interp_list xs (i + 1)
end


@[simp]
lemma interp_raw_zero : interp_raw zero = 0 := by
  simp only [interp_raw]


lemma interp_raw_nil {i : ℕ } : interp_list [] i = 1 := by
  simp only [interp_list]


lemma interp_cons_coprime {xs : List RawProd } {i j: ℕ } (hlt : i < j) : ¬  (Nat.nth Nat.Prime i) ∣ interp_list xs j := by
  induction xs generalizing i j with
  | nil =>
    simp only [interp_raw_nil]
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
      . --apply (ih i) i mismatch...
        have hlt2 : i < (j+1) := by linarith
        apply (ih hlt2)
        assumption
    . exact Nat.prime_nth_prime i




/-- Adding a single zero to the end doesn't change interpretation -/
-- @[simp]
lemma interp_list_append_zero (xs : List RawProd) (k : ℕ) :
    interp_list (xs ++ [zero]) k = interp_list xs k := by
  induction xs generalizing k with
  | nil =>
    simp only [List.nil_append, interp_list, interp_raw]
    rw [pow_zero, one_mul]
  | cons x xs ih =>
    simp only [List.cons_append, interp_list]
    rw [ih]

/-- Adding multiple zeros to the end doesn't change interpretation -/
lemma interp_list_append_zeros (xs : List RawProd) (n k : ℕ) :
    interp_list (xs ++ List.replicate n zero) k = interp_list xs k := by
  induction n with
  | zero => simp only [List.replicate_zero, List.append_nil]
  | succ n ih => rw [List.replicate_succ', ← List.append_assoc, interp_list_append_zero, ih]



/-- A list of all zeros has interpretation 1 -/
lemma interp_allzero_eq_one {xs : List RawProd} {k : ℕ} (h : allzero xs) :
    interp_list xs k = 1 := by
  induction xs generalizing k with
  | nil => simp only [interp_list]
  | cons x xs ih =>
    simp only [interp_list, allzero_iff] at ih h ⊢
    rw [h x List.mem_cons_self, interp_raw, pow_zero, one_mul]
    exact ih fun y hy => h y (List.mem_cons_of_mem x hy)

@[aesop safe]
lemma interp_list_eq_interp_list_trim {xs : List RawProd} {k : ℕ} :
   interp_list (trim xs) k = interp_list xs k := by
  induction xs using List.reverseRecOn with --generalizing k with
  | nil => simp only [trim, List.rdropWhile_nil]
  | append_singleton ys y ih =>
    cases y
    case zero => simp only [trim_append_zero, interp_list_append_zero]; exact ih
    case brak => simp only [trim_append_brak_eq_self]




@[aesop safe]
lemma interp_eq_interp_trim (xs : List RawProd) :
    interp_raw (brak (trim xs)) = interp_raw (brak xs) := by
  simp only [interp_raw]
  exact interp_list_eq_interp_list_trim

mutual
lemma interp_eq_norm_interp : ∀ (x : RawProd), interp_raw (normalize x) = interp_raw x
  | zero => by simp only [normalize, interp_raw_zero]
  | brak xs => by
      simp only [normalize, interp_raw]
      rw [interp_list_eq_interp_list_trim]
      exact interp_list_map_normalize xs 0

lemma interp_list_map_normalize : ∀ (xs : List RawProd) (k : ℕ),
    interp_list (List.map normalize xs) k = interp_list xs k
  | [], _ => by simp only [List.map_nil, interp_list]
  | x :: xs, k => by
      simp only [List.map_cons, interp_list]
      rw [interp_eq_norm_interp x]
      congr 1
      exact interp_list_map_normalize xs (k + 1)
end



theorem equiv_interp_eq {x y : RawProd }: equiv x y → interp_raw x = interp_raw y := by
  revert x y
  apply RawProd.induction₂
  case h_zero_left => intro y h; apply equiv_zero_eq_zero at h; subst h; rfl
  case h_zero_right => intro x h; apply zero_equiv_eq_zero at h; subst h; rfl
  case h_brak_brak =>
    intro xs ys h_interp h_equiv
    simp only [interp_raw]
    simp only [equiv, normalize] at h_equiv
    have h1 : interp_list (trim (List.map normalize xs)) 0 =
              interp_list (trim (List.map normalize ys)) 0 := by simp_all only [brak.injEq]
    simp only [interp_list_eq_interp_list_trim] at h1
    rw [interp_list_map_normalize, interp_list_map_normalize] at h1
    exact h1



lemma interp_list_neq_zero {i : ℕ} (xs : List RawProd): interp_list xs i ≠ 0 := by
  induction xs generalizing i with
  | nil => simp only [interp_list, ne_eq, one_ne_zero, not_false_eq_true]
  | cons x xs ih =>
    simp only [interp_list]
    exact mul_ne_zero (pow_ne_zero _ (Nat.prime_nth_prime i).pos.ne') ih




lemma interp_raw_eq_zero_eq_zero (x : RawProd) (hz : RawProd.interp_raw x = 0) : x = RawProd.zero := by
  match x with
  | zero => simp only
  | brak xs => simp only [interp_raw, interp_list_neq_zero] at hz



/-! ## Bridge Lemma: connecting interp_list to prime factorizations -/

lemma factorization_add {p n m : ℕ} : (n.factorization + m.factorization) p = n.factorization p + m.factorization p := by
  simp only [Nat.factorization, Finsupp.coe_add, Finsupp.coe_mk, Pi.add_apply]

/--
The "Bridge Lemma":
The exponent of the `(k + i)`-th prime in the interpretation of `xs`
is equal to the interpretation of the `i`-th element of `xs`.
-/
@[aesop unsafe]
lemma factorization_interp_list {xs : List RawProd} (k i : ℕ) :
    (interp_list xs k).factorization (Nat.nth Nat.Prime (k + i)) = interp_raw (get xs i) := by
  induction xs generalizing k i with
  | nil =>
    simp only [interp_raw_nil, get_nil, interp_raw_zero]
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
        have hz : (Nat.nth Nat.Prime k ^ x.interp_raw).factorization (Nat.nth Nat.Prime (k + 1 + j)) = 0 := by
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
lemma factorization_interp_list_zero {xs : List RawProd} (i : ℕ) :
    (interp_list xs 0).factorization (Nat.nth Nat.Prime i) = interp_raw (get xs i) := by
  have h := factorization_interp_list (xs := xs) 0 i; simp only [Nat.zero_add] at h; exact h


noncomputable def fromNat : Nat → RawProd
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

end RawProd

namespace QProd

/-- The interpretation function on quotient productive numbers -/
noncomputable def interp : QProd → ℕ :=
  Quotient.lift RawProd.interp_raw @RawProd.equiv_interp_eq


/-! ## Additional useful properties for later proofs -/

lemma interp_mk (x : RawProd) : interp (mk x) = RawProd.interp_raw x := by
  simp only [interp, mk, Quotient.lift_mk]


noncomputable def fromNat (n : ℕ ) := mk (RawProd.fromNat n)

-- silly little lemmas

@[simp] lemma interp_zero : interp zero = 0 := rfl

@[simp] lemma interp_nil : interp (ofList []) = 1 := by
  simp only [interp, ofList, List.map_nil]
  apply Quotient.lift_mk



lemma fromNat_zero : fromNat 0 = zero := by
  simp only [fromNat, RawProd.fromNat, mk_zero_eq_zero]


lemma fromNat_one : fromNat 1 = ofList []  := by
  simp only [fromNat, RawProd.fromNat, mk_nil_eq_nil]

end QProd
