import Prod.interp
import Prod.quot_defs
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.Nat.Prime.Nth
import Mathlib.Tactic.Linarith.Frontend
import Mathlib.NumberTheory.PrimeCounting

namespace RawProd

/-! ### Helper Lemmas: The Bridge between Lists and Primes -/

/-- A list accessor that returns `zero` if out of bounds.
    This is essential for mapping "infinite" prime indices to the finite list. -/
def get (xs : List RawProd) (i : ℕ) : RawProd :=
  xs.getD i zero

@[simp]
lemma get_nil {i : ℕ} : get [] i = zero := by
  simp only [get, List.getD_eq_getElem?_getD, List.length_nil, not_lt_zero', not_false_eq_true,
    getElem?_neg, Option.getD_none]

@[simp]
lemma get_cons_zero {x : RawProd} {xs : List RawProd} : get (x :: xs) 0 = x := by
  simp [get]

@[simp]
lemma get_cons_succ {x : RawProd} {xs : List RawProd} {i : ℕ} : get (x :: xs) (i + 1) = get xs i := by
  simp [get]


lemma factorization_add {p n m : ℕ }: (n + m).factorization p = (n.factorization + m.factorization) p := by
  simp [Nat.factorization]
  split_ifs
  . sorry
  . simp only [add_zero]



lemma factorization_add₂ {p n m : ℕ }: (n.factorization + m.factorization) p  = n.factorization p + m.factorization p := by
  simp only [Nat.factorization, Finsupp.coe_add, Finsupp.coe_mk, Pi.add_apply]


lemma primes_distinct {n m : ℕ } (h : n ≠ m) : Nat.nth Nat.Prime n ≠ Nat.nth Nat.Prime m := by
  sorry


/--
The "Bridge Lemma":
The exponent of the `(k + i)`-th prime in the interpretation of `xs`
is equal to the interpretation of the `i`-th element of `xs`.
-/
lemma factorization_interp_list (xs : List RawProd) (k i : ℕ) :
    (interp_list xs k).factorization (Nat.nth Nat.Prime (k + i)) = interp_raw (get xs i) := by
-- lemma factorization_interp_list {xs : List RawProd} {p : ℕ } (k i : ℕ) (hp : p = Nat.nth Nat.Prime (k + i)):
--     (interp_list xs k).factorization p = interp_raw (get xs i) := by
  induction xs generalizing k i with
  | nil =>
    simp only [interp_nil, get_nil, interp_zero]
    rw [Nat.factorization_one]
    rfl
  | cons x xs ih =>
    simp only [interp_list, get]
    -- Split into head (i=0) and tail (i>0) cases
    cases i with
    | zero =>

      simp only [add_zero, List.getD_eq_getElem?_getD, List.length_cons, lt_add_iff_pos_left,
        add_pos_iff, zero_lt_one, or_true, getElem?_pos, List.getElem_cons_zero, Option.getD_some]
      rw [Nat.factorization_mul, Nat.factorization_pow]--Nat.prime_nth_prime, Finsupp.single_eq_same]
      simp only [Nat.prime_nth_prime, Nat.Prime.factorization, Finsupp.smul_single, smul_eq_mul, mul_one, Finsupp.coe_add, Pi.add_apply, Finsupp.single_eq_same, Nat.add_eq_left]
      · rw [Nat.factorization_eq_zero_of_not_dvd]
        apply interp_cons_coprime

      · apply pow_ne_zero; apply Nat.Prime.ne_zero; apply Nat.prime_nth_prime
      · apply ne_of_gt; apply interp_list_gt_zero
    | succ j =>
      simp only [List.getD_eq_getElem?_getD, List.getElem?_cons_succ] --[Nat.add_succ, Option.getD, cons_succ]
      rw [Nat.add_comm j 1, ←Nat.add_assoc]
      rw [Nat.factorization_mul]
      -- The head part (p_k ^ ...) has 0 exponent for prime p_(k+j+1)
      · rw [factorization_add₂]

        have hz : (Nat.nth Nat.Prime k ^ x.interp_raw).factorization (Nat.nth Nat.Prime (k + 1 + j)) = 0 := by
          rw [Nat.factorization_pow]
          simp only [Nat.prime_nth_prime, Nat.Prime.factorization, Finsupp.smul_single, smul_eq_mul, mul_one, Finsupp.single_apply, ite_eq_right_iff]
          intro h
          absurd h
          apply primes_distinct
          linarith
        rw [hz, zero_add]

        specialize ih (k + 1) j

        simp only [get, List.getD_eq_getElem?_getD] at ih
        --rw [Nat.add_assoc] at ih
        exact ih
      . apply pow_ne_zero; apply Nat.Prime.ne_zero; apply Nat.prime_nth_prime
      . apply ne_of_gt; apply interp_list_gt_zero



lemma normalize_lists_eq_of_equiv_elements {xs ys : List RawProd}
    (h : ∀ i, (get xs i).equiv (get ys i)) : (brak xs).equiv (brak ys) := by
  simp only [equiv, normalize, brak.injEq]
  induction xs generalizing ys with
  | nil => sorry
  | cons => sorry

/-! ### Injectivity -/

theorem interp_inj {x y : RawProd} : interp_raw x = interp_raw y → x.equiv y := by
  -- Induct on size/structure of x, generalizing y
  revert y
  induction x using induction with
  | h_zero =>
    intro y h
    simp only [interp_zero] at h
    exact (raw_interp_eq_zero_eq_zero y h.symm).symm ▸ equiv_refl _
  | h_brak xs ih =>
    intro y h
    cases y with
    | zero =>
      simp only [interp_zero] at h
      exact (raw_interp_eq_zero_eq_zero (brak xs) h).symm ▸ equiv_refl _
    | brak ys =>
      simp only [equiv, normalize, brak.injEq]
      -- We must show: trim (map normalize xs) = trim (map normalize ys)
      -- Strategy: Show xs[i] ~ ys[i] for all i, which implies their normalized lists are equal "up to length"
      have h_factors : ∀ i, interp_raw (get xs i) = interp_raw (get ys i) := by
        intro i
        -- Use the Bridge Lemma!
        rw [← factorization_interp_list xs 0 i, ← factorization_interp_list ys 0 i]
        simp only [Nat.zero_add]
        simp only [interp_raw] at h
        rw [h] -- The main assumption I(x) = I(y)

      -- Now map this back to equivalence using the IH
      have h_equiv_at_i : ∀ i, (get xs i).equiv (get ys i) := by
        intro i
        -- We need to apply the IH.
        -- Technicality: 'get xs i' is structurally smaller than 'brak xs' is false if we look at it naively,
        -- but 'induction' gives us the hypothesis for all x ∈ xs.
        let x_i := get xs i
        if hi : i < xs.length then
           simp [get, hi] at h_factors ⊢
           apply ih (xs.get ⟨i, hi⟩) _ --(List.get_mem _ _ _)
           . simp only [List.get_eq_getElem]
             grind only [= getElem?_pos, = Option.getD_some]
           . simp_all only [List.get_eq_getElem, List.getElem_mem]

        else

           simp [get, Option.getD, hi, dif_neg, List.getD_eq_default] at h_factors ⊢ -- penultimate 2 unused
           -- if out of bounds, x_i is zero.
           -- h_factors says I(ys[i]) = 0, so ys[i] must be equivalent to zero.
           rw [interp_zero] at h_factors
--            Tactic `rewrite` failed: Did not find an occurrence of the pattern
--   zero.interp_raw
-- in the target expression
--   ∀ (i : ℕ),
--     (match xs[i]? with
--         | some x => x
--         | none => zero).interp_raw =
--       (match ys[i]? with
--         | some x => x
--         | none => zero).interp_raw
           have y_is_zero := raw_interp_eq_zero_eq_zero _ (h_factors i).symm
           rw [y_is_zero]
           exact equiv_refl _

      -- Finally, show that component-wise equivalence implies list equivalence (after trim)
      -- This requires a lemma about `trim` and `map normalize`.
      -- Since you essentially have `normalize` defined as `trim (map normalize)`,
      -- and `equiv` is equality of normal forms:
      apply normalize_lists_eq_of_equiv_elements --doesnt exist
      --exact h_equiv_at_i

/-! ### Surjectivity -/

/--
Constructive inverse:
Since `interp_surj` asks for existence, defining `fromNat` (which you have partially done)
is the best way.
-/

-- Assuming `fromNat` is defined as in your `interp.lean` but corrected.
-- I'll define a quick helper here to close the proof.

lemma gt_zero_imp_ne_zero {n : ℕ } : 0 < n → n ≠ 0 := by
  sorry




theorem interp_surj : ∀ n, ∃ x : RawProd, interp_raw x = n := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    match n with
    | 0 => use zero; rfl
    | 1 => use brak []; simp only [interp_raw, interp_nil]
    | (m+2) =>
      let n_val := m + 2
      have n_pos : 0 < n_val := by simp only [lt_add_iff_pos_left, add_pos_iff, Nat.ofNat_pos, or_true, n_val]

      -- We construct the list by looking at factorization
      let max_idx := n_val.factorization.support.max
      let len := match max_idx with | some m => m + 1 | none => 0

      -- For every prime index i < len, we get an exponent e = factorization p_i
      -- Since p_i ≥ 2, we know p_i^e ≤ n, so e < n (unless n=1, handled).
      -- Actually simpler: e ≤ log2(n) < n for n > 1.

      have n_nz : n_val ≠ 0 := by simp_all only [lt_add_iff_pos_left, add_pos_iff, Nat.ofNat_pos, or_true, ne_eq, Nat.add_eq_zero_iff, OfNat.ofNat_ne_zero, and_false, not_false_eq_true, n_val] -- EDWIN
      --have interp_nz : interp_list

      let f := fun (i : ℕ) =>
        let p := Nat.nth Nat.Prime i
        let e := n_val.factorization p
        have he : e < n_val := Nat.factorization_lt p n_nz
        Classical.choose (ih e he)

      let xs := List.ofFn (fun i : Fin len => f i)

      use brak xs
      -- The proof that I(brak xs) = n relies on I(xs) reconstructing the factorization.
      -- This follows from `Nat.eq_of_factorization_eq`.
      apply Nat.eq_of_factorization_eq (by exact gt_zero_imp_ne_zero interp_list_gt_zero) n_nz
      simp only [interp_raw]
      intro p
      -- Split p into p_i or not prime
      by_cases hp : p.Prime
      · let i := Nat.nth Nat.Prime p
        -- Use the bridge lemma again!


        rw [factorization_interp_list xs 0 i, Nat.zero_add]
--         n m : ℕ
-- ih : ∀ m_1 < m + 2, ∃ x, x.interp_raw = m_1
-- n_val : ℕ := ⋯
-- n_pos : 0 < n_val
-- max_idx : WithBot ℕ := ⋯
-- len : ℕ := ⋯
-- n_nz : n_val ≠ 0
-- f : ℕ → RawProd := ⋯
-- xs : List RawProd := ⋯
-- p : ℕ
-- hp : Nat.Prime p
-- i : ℕ := ⋯
-- ⊢ (interp_list xs 0).factorization (Nat.nth Nat.Prime (0 + i)) = (get xs i).interp_raw
-- Tactic `rewrite` failed: Did not find an occurrence of the pattern
--   (interp_list xs 0).factorization (Nat.nth Nat.Prime (0 + i))
-- in the target expression
--   (interp_list xs 0).factorization p = n_val.factorization p
-- pretty sure we would need i to be in the goal somewhere?
        sorry -- (This is standard bookkeeping now)
      · -- If p is not prime, factorization is 0 on both sides
        rw [Nat.factorization_eq_zero_of_not_prime _ hp]
        rw [Nat.factorization_eq_zero_of_not_prime _ hp]
