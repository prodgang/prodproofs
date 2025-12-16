import Prod.raw_defs
import Prod.quot_defs
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


lemma interp_zero : interp_raw zero = 0 := by
  simp only [interp_raw]


lemma interp_nil {i : ℕ } : interp_list [] i = 1 := by
  simp only [interp_list]


-- lemma interp_list_cons {x : RawProd} {xs : List RawProd} {i : ℕ } : interp_list (x::xs) i = Nat.nth  * interp_list xs (i+1) := by
--   simp only [interp_list, mul_one]

-- lemma prime_gt_one {p : ℕ } (hp : Nat.Prime p) : 1 < p := by
--   sorry

lemma primes_distinct {n m : ℕ } (h : n ≠ m) : Nat.nth Nat.Prime n ≠ Nat.nth Nat.Prime m := by
  sorry

lemma interp_cons_coprime {xs : List RawProd } {i j: ℕ } (hlt : i < j) : ¬  (Nat.nth Nat.Prime i) ∣ interp_list xs j := by
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

@[aesop safe]
lemma interp_eq_norm_interp {x : RawProd} :  interp_raw (normalize x) = interp_raw x := by
  induction x using RawProd.induction with
  | h_zero => simp only [normalize_zero_eq_zero]
  | h_brak xs ih =>
    simp_all [normalize, interp_raw]
    sorry
    --exact interp_list_eq_interp_list_trim xs 0
    -- cant close, skipping for now
--      ∀ x ∈ xs, x.normalize.interp_raw = x.interp_raw
-- ⊢ interp_list (trim (List.map normalize xs)) 0 = interp_list xs 0




lemma interp_list_map_normalize {xs : List RawProd} {k : ℕ} :
    interp_list (List.map normalize xs) k = interp_list xs k := by
  induction xs generalizing k with
  | nil => simp only [List.map_nil, interp_list]
  | cons x xs ih =>
    simp only [List.map_cons, interp_list]
    rw [interp_eq_norm_interp, ih] -- old
    --rw [ih]
    --simp [ih]
    --left



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
    simp [interp_list_eq_interp_list_trim] at h1
    rw [interp_list_map_normalize, interp_list_map_normalize] at h1
    exact h1



lemma interp_list_singleton (x : RawProd) (i : ℕ ) : 0 < interp_list [x] i := by
  simp [interp_list]
  have hnope : 0 < Nat.nth Nat.Prime i := by simp [Nat.prime_nth_prime, Nat.Prime.pos]
  simp_all only [pow_pos]


lemma interp_list_gt_zero {xs : List RawProd} {i : ℕ} : 0 < interp_list xs i := by
  induction xs generalizing i with
  | nil => simp only [interp_list, zero_lt_one]
  | cons x xs ih =>
    simp only [interp_list]
    apply mul_pos
    · apply Nat.pow_pos
      apply Nat.Prime.pos
      apply Nat.prime_nth_prime
    · apply ih




lemma interpraw_eq_zero_eq_zero (x : RawProd) (hz : RawProd.interp_raw x = 0) : x = RawProd.zero := by
  match x with
  | zero => simp only
  | brak xs =>
    simp [interp_raw] at hz
    absurd hz
    have hgtz : 0 < interp_list xs 0 := interp_list_gt_zero
    simp_all only [lt_self_iff_false]



noncomputable def fromNat : Nat → RawProd
  | 0 => zero
  | 1 => brak []
  | n@(Nat.succ _) =>
      -- Get the list of prime factors and determine the maximum prime factor
      -- let factor_map := Nat.primeFactorsList n
      -- let max_prime := factor_map.foldl (fun acc p => max acc p) 2
      -- let max_index := (factor_map.idxOf max_prime) + 1
      let max_index := n -- crazy crude bound

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




-- FROMNAT

-- noncomputable def fromNat : Nat → QProd
--   | 0 => zero
--   | 1 => ofList []
--   | n@(Nat.succ _) =>
--       -- Get the list of prime factors and determine the maximum prime factor
--       let factor_map := Nat.primeFactorsList n
--       let max_prime := factor_map.foldl (fun acc p => max acc p) 2
--       let max_index := (factor_map.idxOf max_prime) + 1

--       have n_neq_0: n ≠ 0 := by simp?; sorry

--       ofList (List.map (λi => fromNat (n.factorization (Nat.nth Nat.Prime i))) (List.range max_index))

-- termination_by n => n
-- decreasing_by
--   rename_i n2 h
--   simp only [namedPattern, Nat.succ_eq_add_one, gt_iff_lt]
--   have h2 : n = n2 + 1 := by sorry
--   rw [← h2]
--   exact Nat.factorization_lt (Nat.nth Nat.Prime i) n_neq_0

noncomputable def fromNat (n : ℕ ) := mk (RawProd.fromNat n)

-- silly little lemmas

@[simp] lemma interp_zero : interp zero = 0 := rfl

@[simp] lemma interp_nil : interp (ofList []) = 1 := by
  simp only [interp, ofList, List.map_nil]
  apply Quotient.lift_mk



-- @[simp]
-- lemma interp_eq_zero_eq_zero (x : QProd) (hz : interp x = 0) : x = zero := by
--   -- apply Quotient.in
--   -- intro r
--   -- have : RawProd.interp_raw r = 0 := by
--   --   simp [interp, Quotient.liftOn] at hz
--   --   exact hz
--   -- rw [RawProd.raw_interp_eq_zero_eq_zero r this]
--   -- --apply Quotient.sound
--   -- --apply RawProd.equiv.refl
--   -- simp only [RawProd.interp_zero, brak_eq_mk]
--   apply Quot.recOn
--   . sorry
--   . sorry

  -- shouldnt be so hard!!
  -- probably need better mechanics for lifting to quotient


lemma fromNat_zero : fromNat 0 = zero := by
  simp only [fromNat, RawProd.fromNat, mk_zero_eq_zero]


lemma fromNat_one : fromNat 1 = ofList []  := by
  simp only [fromNat, RawProd.fromNat, mk_nil_eq_nil]

end QProd
