import Prod.raw_defs
import Prod.quot_defs3
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Nat.Nth
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.NumberTheory.PrimeCounting

namespace RawProd

/-- Raw interpretation function -/
noncomputable def interpRaw : RawProd → ℕ
  | zero => 0
  | cons xs => interpList xs 0
where
  interpList : List RawProd → ℕ → ℕ
    | [], _ => 1
    | x :: xs, i => (Nat.nth Nat.Prime i) ^ interpRaw x * interpList xs (i + 1)

/-! ## Basic lemmas about trailing zeros -/




/-- Adding a single zero to the end doesn't change interpretation -/
lemma interpList_append_zero (xs : List RawProd) (k : ℕ) :
    interpRaw.interpList (xs ++ [zero]) k = interpRaw.interpList xs k := by
  induction xs generalizing k with
  | nil =>
    simp only [List.nil_append, interpRaw.interpList, interpRaw]
    rw [pow_zero, one_mul]
  | cons x xs ih =>
    simp only [List.cons_append, interpRaw.interpList]
    rw [ih]

/-- Adding multiple zeros to the end doesn't change interpretation -/
lemma interpList_append_zeros (xs : List RawProd) (n k : ℕ) :
    interpRaw.interpList (xs ++ List.replicate n zero) k = interpRaw.interpList xs k := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.replicate_succ', ← List.append_assoc, interpList_append_zero, ih]

/-! ## Properties of trim (removeTrailingZeros) -/

/-- A list trims to empty iff all elements are zero -/
lemma trim_eq_nil_iff (xs : List RawProd) :
    trim xs = [] ↔ ∀ x ∈ xs, x = zero := by
  induction xs with
  | nil =>
    simp only [trim, List.not_mem_nil, IsEmpty.forall_iff, implies_true]
  | cons x xs ih =>
    simp only [trim]
    split
    next h => -- removeTrailingZeros xs = []
      split_ifs with hx
      · -- x == zero is true
        simp only [List.mem_cons, forall_eq_or_imp]
        constructor
        · intro _
          constructor
          · -- Need to show x = RawProd.zero from x == RawProd.zero
            exact beq_iff_eq.mp hx
          · exact ih.mp h
        · simp only [implies_true]
      · -- x == zero is false
        simp only [List.mem_cons, forall_eq_or_imp]
        constructor
        · intro h_eq; cases h_eq
        · intro ⟨h_x_zero, _⟩
          exact absurd ((beq_iff_eq).mpr h_x_zero) hx
    next ys h => -- removeTrailingZeros xs = y :: ys
      simp only [List.mem_cons, forall_eq_or_imp]
      constructor
      · intro h_eq; cases h_eq
      · intro ⟨h_x, h_xs⟩
        have : trim xs = [] := ih.mpr h_xs
        rw [this] at h
        absurd h
        rfl

/-- A list of all zeros has interpretation 1 -/
lemma interpList_all_zeros (xs : List RawProd) (k : ℕ) (h : ∀ x ∈ xs, x = zero) :
    interpRaw.interpList xs k = 1 := by
  induction xs generalizing k with
  | nil => simp only [interpRaw.interpList]
  | cons x xs ih =>
    simp only [interpRaw.interpList]
    rw [h x List.mem_cons_self, interpRaw, pow_zero, one_mul]
    exact ih (k + 1) fun y hy => h y (List.mem_cons_of_mem x hy)

/-! ## Main result: interpretation respects trimming -/

/-- Interpretation equals interpretation of trimmed list at any starting index -/
@[aesop safe]
lemma interpList_eq_interpList_trim (xs : List RawProd) (k : ℕ) :
   interpRaw.interpList (trim xs) k = interpRaw.interpList xs k := by
  induction xs generalizing k with
  | nil => simp only [trim]
  | cons x xs ih =>
    simp only [trim]
    split
    next h => -- trim xs = []
      have h_all_zero : ∀ y ∈ xs, y = zero := trim_eq_nil_iff xs |>.mp h
      split_ifs with hx
      · -- x == zero, so trim returns []
        simp only [interpRaw.interpList]
        rw [interpList_all_zeros xs (k + 1) h_all_zero]
        rw [beq_iff_eq.mp hx, interpRaw, pow_zero, one_mul]
      · -- x ≠ zero, so trim returns [x]
        simp only [interpRaw.interpList]
        rw [interpList_all_zeros xs (k + 1) h_all_zero]
    next ys h => -- trim xs = y :: ys
      simp only [interpRaw.interpList]
      congr 1
      exact ih (k + 1)


@[aesop safe]
lemma interp_eq_interp_trim (xs : List RawProd) :
    interpRaw (cons (trim xs)) = interpRaw (cons xs) := by
  simp only [interpRaw]
  exact interpList_eq_interpList_trim xs 0

@[simp]
lemma equiv_zero_eq_zero (x : RawProd) (hequiv : equiv zero x) : x = zero := by
  simp [equiv] at hequiv
  cases x
  case zero => rfl
  case cons xs => simp_all only [normalize, reduceCtorEq]


@[simp]
lemma zero_equiv_eq_zero (x : RawProd) (hequiv : equiv x zero) : x = zero := by
  simp [equiv] at hequiv
  cases x
  case zero => rfl
  case cons xs => simp_all only [normalize, reduceCtorEq]

@[aesop safe]
lemma interp_eq_norm_interp (x : RawProd) :  interpRaw (normalize x) = interpRaw x := by
  induction x using RawProd.induction with
  | h_zero => simp [normalize]
  | h_cons xs ih =>
    simp [normalize, interpRaw]
    sorry
    --exact interpList_eq_interpList_trim xs 0
    -- cant close, skipping for now
--      ∀ x ∈ xs, x.normalize.interpRaw = x.interpRaw
-- ⊢ interpRaw.interpList (trim (List.map normalize xs)) 0 = interpRaw.interpList xs 0




lemma interpList_map_normalize (xs : List RawProd) (k : ℕ) :
    interpRaw.interpList (List.map normalize xs) k = interpRaw.interpList xs k := by
  induction xs generalizing k with
  | nil => simp only [List.map_nil, interpRaw.interpList]
  | cons x xs ih =>
    simp only [List.map_cons, interpRaw.interpList]
    rw [interp_eq_norm_interp, ih] -- old
    --rw [ih]
    --simp [ih]
    --left



theorem equiv_interp_eq : ∀ x y, equiv x y → interpRaw x = interpRaw y := by
  apply RawProd.induction₂
  case h_zero_left => intro y h; apply equiv_zero_eq_zero at h; subst h; rfl
  case h_zero_right => intro x h; apply zero_equiv_eq_zero at h; subst h; rfl
  case h_cons_cons =>
    intro xs ys h_interp h_equiv
    simp only [interpRaw]
    simp only [equiv, normalize] at h_equiv
    -- h_equiv : cons trim (List.map normalize xs) = cons trim (List.map normalize ys)
    have h1 : interpRaw.interpList (trim (List.map normalize xs)) 0 =
              interpRaw.interpList (trim (List.map normalize ys)) 0 := by
      simp_all only [cons.injEq]
    rw [interpList_eq_interpList_trim (List.map normalize xs) 0] at h1
    rw [interpList_eq_interpList_trim (List.map normalize ys) 0] at h1
    rw [interpList_map_normalize xs 0] at h1
    rw [interpList_map_normalize ys 0] at h1
    exact h1



-- silly lemmas

@[simp]
lemma interp_zero : interpRaw zero = 0 := by
  simp only [interpRaw]

@[simp]
lemma interp_nil : interpRaw (cons []) = 1 := by
  simp only [interpRaw, interpRaw.interpList]

@[simp]
lemma interpList_nil (i : ℕ ): interpRaw.interpList [] i = 1 := by
  simp [interpRaw.interpList]

@[simp]
lemma interpList_singleton (x : RawProd) (i : ℕ ) : 0 < interpRaw.interpList [x] i := by
  simp [interpRaw.interpList]
  have hnope : 0 < Nat.nth Nat.Prime i := by simp [Nat.prime_nth_prime, Nat.Prime.pos]
  simp_all only [pow_pos]

@[aesop unsafe] lemma interp_cons_eq_interp_mult (x : RawProd) (xs : List RawProd) (i : ℕ ) : interpRaw.interpList (x::xs) i = interpRaw.interpList [x] i * interpRaw.interpList xs i+1 := by
  sorry

@[aesop unsafe] lemma interpList_gt_zero (xs : List RawProd) (i : ℕ ) : 0 < interpRaw.interpList xs i := by
  induction xs generalizing i with
  | nil => simp only [interpList_nil, zero_lt_one]
  | cons y ys ih => rw [interp_cons_eq_interp_mult]
                    --have hl : 0 < interpRaw.interpList [y] i := by simp only [interpList_singleton]
                    simp only [lt_add_iff_pos_left, add_pos_iff, interpList_singleton,
                      mul_pos_iff_of_pos_left, zero_lt_one, or_true]





@[simp] lemma raw_interp_eq_zero_eq_zero (x : RawProd) (hz : RawProd.interpRaw x = 0) : x = RawProd.zero := by
  match x with
  | zero => simp
  | cons [] => simp [interpRaw] at hz
  | cons (x::xs) => rename_i y
                    rw [interpRaw, interp_cons_eq_interp_mult] at hz
                    simp only [Nat.add_eq_zero, mul_eq_zero, one_ne_zero, and_false] at hz




end RawProd

namespace QProd

/-- The interpretation function on quotient productive numbers -/
noncomputable def interp : QProd → ℕ :=
  Quotient.lift RawProd.interpRaw RawProd.equiv_interp_eq


/-! ## Additional useful properties for later proofs -/

theorem interp_mk (x : RawProd) : interp (mk x) = RawProd.interpRaw x := by
  simp only [interp, mk, Quotient.lift_mk]




-- FROMNAT

/-- Extract the exponent of the i-th prime in n's factorization -/

noncomputable def fromNat : Nat → QProd
  | 0 => zero
  | 1 => ofList []
  | n@(Nat.succ _) =>
      -- Get the list of prime factors and determine the maximum prime factor
      let factor_map := Nat.primeFactorsList n
      let max_prime := factor_map.foldl (fun acc p => max acc p) 2
      let max_index := (factor_map.idxOf max_prime) + 1

      have n_neq_0: n ≠ 0 := by linarith

      ofList (List.map (λi => fromNat (n.factorization (Nat.nth Nat.Prime i))) (List.range max_index))

termination_by n => n
decreasing_by
  rename_i n2 h
  simp only [namedPattern, Nat.succ_eq_add_one, gt_iff_lt]
  have h2 : n = n2 + 1 := by linarith
  rw [← h2]
  exact Nat.factorization_lt (Nat.nth Nat.Prime i) n_neq_0



-- silly little lemmas

@[simp] lemma interp_zero : interp zero = 0 := rfl

@[simp] lemma interp_nil : interp (ofList []) = 1 := by
  simp only [interp, ofList, List.map_nil]
  apply Quotient.lift_mk



@[simp]
lemma interp_eq_zero_eq_zero (x : QProd) (hz : interp x = 0) : x = zero := by
  -- apply Quotient.in
  -- intro r
  -- have : RawProd.interpRaw r = 0 := by
  --   simp [interp, Quotient.liftOn] at hz
  --   exact hz
  -- rw [RawProd.raw_interp_eq_zero_eq_zero r this]
  -- --apply Quotient.sound
  -- --apply RawProd.equiv.refl
  -- simp only [RawProd.interp_zero, brak_eq_mk]
  apply Quot.recOn
  . sorry
  . sorry

  -- shouldnt be so hard!!
  -- probably need better mechanics for lifting to quotient





@[simp]
lemma fromNat_zero : fromNat 0 = zero := by
  simp [fromNat]


@[simp]
lemma fromNat_one : fromNat 1 = ofList []  := by
  simp [fromNat]

end QProd
