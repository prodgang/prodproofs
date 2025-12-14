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
  simp only [get, List.getD_eq_getElem?_getD, List.getElem?_cons_succ]


lemma factorization_add {p n m : ℕ }: (n.factorization + m.factorization) p  = n.factorization p + m.factorization p := by
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
      · rw [factorization_add]

        have hz : (Nat.nth Nat.Prime k ^ x.interp_raw).factorization (Nat.nth Nat.Prime (k + 1 + j)) = 0 := by
          rw [Nat.factorization_pow]
          simp only [Nat.prime_nth_prime, Nat.Prime.factorization, Finsupp.smul_single, smul_eq_mul, mul_one, Finsupp.single_apply, ite_eq_right_iff]
          intro h
          absurd h
          apply primes_distinct -- only remaining sorry
          linarith
        rw [hz, zero_add]
        specialize ih (k + 1) j
        simp only [get, List.getD_eq_getElem?_getD] at ih
        exact ih
      . apply pow_ne_zero; apply Nat.Prime.ne_zero; apply Nat.prime_nth_prime
      . apply ne_of_gt; apply interp_list_gt_zero




lemma brak_equiv_elementwise {xs ys : List RawProd}
    (h : ∀ i, (get xs i).equiv (get ys i)) : (brak xs).equiv (brak ys) := by
  induction xs generalizing ys with
  | nil =>
    simp only [equiv, normalize, List.map_nil, brak.injEq]
    simp only [trim, List.rdropWhile_nil, List.nil_eq, List.rdropWhile_eq_nil_iff, List.mem_map, beq_iff_eq, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂]
    intro y hy
    suffices hyz : y = zero by rw [hyz, normalize_zero_eq_zero]
    obtain ⟨n, hn⟩ := (List.mem_iff_get.mp hy)
    specialize h n
    simp only [get, List.getD_nil] at h
    apply equiv_zero_eq_zero at h
    subst hn
    simp_all only [List.getD_eq_getElem?_getD, Fin.is_lt, getElem?_pos, Option.getD_some, List.get_eq_getElem]

  | cons x xs ih =>
    cases ys with
    | nil =>
      --same as above
      simp only [equiv, normalize, List.map_nil, brak.injEq]
      simp only [trim, List.rdropWhile_nil, List.rdropWhile_eq_nil_iff, List.mem_map, beq_iff_eq, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂]
      intro x hx
      suffices hxz : x = zero by rw [hxz, normalize_zero_eq_zero]
      obtain ⟨n, hn⟩ := (List.mem_iff_get.mp hx)
      specialize h n
      simp only [get, List.getD_nil] at h
      apply zero_equiv_eq_zero at h
      subst hn
      simp_all only [List.getD_eq_getElem?_getD, Fin.is_lt, getElem?_pos, Option.getD_some, List.get_eq_getElem]
    | cons y ys =>
      apply cons_equiv_cons
      . specialize h 0
        rw [get_cons_zero, get_cons_zero] at h
        exact h
      . apply ih
        intro i
        specialize h (i+1)
        simp only [get_cons_succ] at h
        exact h


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
      have h_factors : ∀ i, interp_raw (get xs i) = interp_raw (get ys i) := by
        intro i
        -- Use the Bridge Lemma!
        rw [← factorization_interp_list xs 0 i, ← factorization_interp_list ys 0 i]
        simp only [Nat.zero_add]
        simp only [interp_raw] at h
        rw [h]

      apply brak_equiv_elementwise

      intro i
      let x_i := get xs i
      if hi : i < xs.length then
          simp only [get, List.getD_eq_getElem?_getD, hi, getElem?_pos, Option.getD_some] at h_factors ⊢
          apply ih (xs.get ⟨i, hi⟩) _
          . simp only [List.get_eq_getElem]
            grind only [= getElem?_pos, = Option.getD_some]
          . simp_all only [List.get_eq_getElem, List.getElem_mem]

      else
          specialize h_factors i
          simp only [get, List.getD_eq_getElem?_getD, hi, not_false_eq_true, getElem?_neg, Option.getD_none] at h_factors ⊢
          rw [interp_zero] at h_factors
          have y_is_zero := raw_interp_eq_zero_eq_zero _ (h_factors).symm
          rw [y_is_zero]
          exact equiv_refl _


/-! ### Surjectivity -/

lemma gt_zero_imp_ne_zero {n : ℕ } : 0 < n → n ≠ 0 := by
  --linarith
  sorry

lemma prime_index {p : ℕ } (hp : Nat.Prime p) : ∃ i, p = Nat.nth Nat.Prime i := by
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
      ·
        obtain ⟨i, hi⟩ := prime_index hp
        -- actually want i, such that nth Prime i = p


        rw [hi]
        rw [← Nat.zero_add i, factorization_interp_list xs 0 i]
        rw [Nat.zero_add]
--         proof state:
-- n m : ℕ
-- ih : ∀ m_1 < m + 2, ∃ x, x.interp_raw = m_1
-- n_val : ℕ := m + 2
-- n_pos : 0 < n_val
-- max_idx : WithBot ℕ := n_val.factorization.support.max
-- len : ℕ := match max_idx with
-- | some m => m + 1
-- | none => 0
-- n_nz : n_val ≠ 0
-- f : ℕ → RawProd := fun i ↦
--   let p := Nat.nth Nat.Prime i;
--   let e := n_val.factorization p;
--   have he := ⋯;
--   Classical.choose ⋯
-- xs : List RawProd := List.ofFn fun i ↦ f ↑i
-- p : ℕ
-- hp : Nat.Prime p
-- i : ℕ
-- hi : p = Nat.nth Nat.Prime i
-- ⊢ (get xs i).interp_raw = n_val.factorization (Nat.nth Nat.Prime i)
        -- almost there but im a bit sceptical about this choice stuff
        sorry
      · -- If p is not prime, factorization is 0 on both sides
        rw [Nat.factorization_eq_zero_of_not_prime _ hp]
        rw [Nat.factorization_eq_zero_of_not_prime _ hp]




lemma factorization_lt_self {n p : ℕ} (hn : 2 ≤ n) : n.factorization p < n := by
  by_cases hp : n.factorization p = 0
  · rw [hp]
    exact lt_of_lt_of_le (by decide) hn
  · sorry
    -- have h_div : p ^ n.factorization p ∣ n := Nat.ord_proj_dvd n p
    -- have h_le : p ^ n.factorization p ≤ n := Nat.le_of_dvd (gt_zero_imp_ne_zero (lt_of_lt_of_le (by decide) hn)) h_div
    -- have p_ge_2 : p ≥ 2 := Nat.Prime.two_le (Nat.prime_of_mem_factorization (Nat.mem_factorization.mpr (Nat.pos_of_ne_zero hp)))

    -- -- We know 2^k > k for all k. Hence if fact >= n, then p^fact >= 2^fact >= 2^n > n, contradiction.
    -- by_contra h_contra
    -- push_neg at h_contra
    -- have h_pow : 2 ^ n.factorization p ≤ p ^ n.factorization p := Nat.pow_le_pow_left p_ge_2 _
    -- have h_strict : n < 2 ^ n := Nat.lt_pow_self (by decide) n
    -- have h_final : n < 2 ^ n.factorization p := lt_of_lt_of_le h_strict (Nat.pow_le_pow_right (by decide) h_contra)
    -- linarith


noncomputable def fromNat : Nat → RawProd
  | 0 => zero
  | 1 => brak []
  | n@(Nat.succ _) =>
      -- Get the list of prime factors and determine the maximum prime factor
      --let factor_map := Nat.primeFactorsList n
      --let max_prime := factor_map.foldl (fun acc p => max acc p) 2
      let factor_map := Nat.primeFactorsList n
      let max_prime := factor_map.foldl (fun acc p => max acc p) 2
      let max_index := (factor_map.idxOf max_prime) + 1
      --let max_idx := n.factorization.support.max make not Bot

      have n_neq_0: n ≠ 0 := by simp?; sorry

      --brak (List.map (λi => fromNat (n.factorization (Nat.nth Nat.Prime i))) (List.range max_index))
      brak (List.map (fun i => fromNat (n.factorization (Nat.nth Nat.Prime i))) (List.range max_index))

termination_by n => n
decreasing_by
  rename_i n2 h
  simp only [namedPattern, Nat.succ_eq_add_one, gt_iff_lt]
  have h2 : n = n2 + 1 := by sorry
  rw [← h2]
  exact Nat.factorization_lt (Nat.nth Nat.Prime i) n_neq_0




-- gemini nonsense. use of prod_pow_factorization_eq_self is very interesting tho
-- or maybe Nat.factorizationEquiv?
-- theorem interp_fromNat (n : ℕ) : interp_raw (fromNat n) = n := by
--    induction n using Nat.strong_induction_on with
--    | h n ih =>
--     --unfold fromNat
--     match n with
--     | 0 => simp only [fromNat, interp_zero]
--     | 1 => simp only [fromNat, interp_raw, interp_nil]
--     | (m+2) =>

--     simp only [fromNat, Nat.succ_eq_add_one]



--     -- We need to prove: interp_list (List.ofFn ...) 0 = n
--     -- We know n = ∏ p_i ^ e_i. We will show the LHS matches this product.

--     -- 1. Setup the equality with prime factorization
--     have n_pos : n ≠ 0 := by sorry
--     --conv_rhs => rw [← Nat.prod_pow_factorization_eq_self n_pos]

--     -- 2. Identify the terms in the interp_list product
--     -- The interp_list of a list constructed by `ofFn f` corresponds to ∏ p_i ^ interp(f i)
--     -- We'll match this to Finsupp.prod

--     -- Let's define the support of the product.
--     -- The LHS is effectively ∏_{i < n} p_i ^ (interp (fromNat (factors p_i)))
--     -- By IH, interp (fromNat e) = e. So LHS = ∏_{i < n} p_i ^ (factors p_i)

--     -- We need to show this finite product equals the Finsupp product (which is over all primes).
--     -- It suffices to show that for all i ≥ n, factors p_i = 0.

--     rw [interp_list] -- This unfolds one step, but interp_list is recursive.
--     -- Instead of unfolding manually, let's use the property of interp_list with `get`
--     -- But we don't have a lemma relating `interp_list` of `ofFn` directly to `Finset.prod`.
--     -- Let's assume a "correctness of construction" approach via factorization uniqueness.

--     apply Nat.eq_of_factorization_eq (gt_zero_imp_ne_zero interp_list_gt_zero) n_pos
--     intro p

--     -- Let's find the exponent of p in the LHS (interp_list ...)
--     let xs := List.ofFn (fun i : Fin n => fromNat (n.factorization (Nat.nth Nat.Prime i)))

--     by_cases hp : Nat.Prime p
--     · obtain ⟨i, hi⟩ := prime_index hp
--       rw [hi]

--       -- Apply the Bridge Lemma (factorization_interp_list)
--       rw [← Nat.zero_add i]
--       rw [factorization_interp_list xs 0 i]
--       rw [Nat.zero_add]

--       -- Now we evaluate `(get xs i).interp_raw`
--       simp only [List.get_ofFn, Fin.cast_eq_self, xs]

--       if hi_bound : i < n then
--         -- Case 1: i is within the list bounds
--         rw [List.get_ofFn]
--         · -- Apply Inductive Hypothesis
--           simp only
--           apply ih
--           -- Proof that exponent < n (for termination/induction)
--           simp at h_lt
--           apply factorization_lt_self h_lt
--         · exact hi_bound
--       else
--         -- Case 2: i is outside the list bounds
--         -- LHS: `get` returns `zero` (default), so interp is 0
--         rw [not_lt] at hi_bound
--         have h_get_zero : get xs i = zero := by
--           unfold get
--           rw [List.getD_eq_default]
--           simp only [xs, List.length_ofFn]
--           exact hi_bound

--         rw [h_get_zero, interp_zero]

--         -- RHS: We must show n.factorization p = 0
--         -- p = p_i. Since i ≥ n and p_i ≥ i+1, we have p ≥ n+1 > n.
--         -- A number n cannot have a prime factor p > n (unless n=0, but n≥2).
--         apply Nat.factorization_eq_zero_of_lt
--         calc
--           n < n + 1 := Nat.lt_succ_self n
--           _ ≤ i + 1 := Nat.add_le_add_right hi_bound 1
--           _ ≤ Nat.nth Nat.Prime i := Nat.succ_le_nth Nat.Prime i
--           _ = p := hi.symm

--     · -- If p is not prime, both factorizations are 0
--       rw [Nat.factorization_eq_zero_of_not_prime _ hp]
--       rw [Nat.factorization_eq_zero_of_not_prime _ hp]
