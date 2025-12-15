import Prod.interp
import Prod.quot_defs
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.Nat.Prime.Nth
import Mathlib.Tactic.Linarith.Frontend
import Mathlib.NumberTheory.PrimeCounting

namespace RawProd

/-! ### Helper Lemmas: The Bridge between Lists and Primes -/


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


-- couple of lemmas that really shouldnt be my responsibility

lemma prime_index {p : ℕ } (hp : Nat.Prime p) : ∃ i, p = Nat.nth Nat.Prime i := by
  sorry

lemma prime_index_lt {i : ℕ } : i < Nat.nth Nat.Prime i := by
  sorry


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
      apply cons_equiv_cons_iff.mp
      constructor
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
    exact (interpraw_eq_zero_eq_zero y h.symm).symm ▸ equiv_refl
  | h_brak xs ih =>
    intro y h
    cases y with
    | zero =>
      simp only [interp_zero] at h
      exact (interpraw_eq_zero_eq_zero (brak xs) h).symm ▸ equiv_refl
    | brak ys =>
      have h_factors : ∀ i, interp_raw (get xs i) = interp_raw (get ys i) := by
        intro i
        -- Use the Bridge Lemma!
        rw [← factorization_interp_list 0 i, ← factorization_interp_list 0 i]
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
          have y_is_zero := interpraw_eq_zero_eq_zero _ (h_factors).symm
          rw [y_is_zero]
          exact equiv_refl


/-! ### Surjectivity -/



theorem interp_fromNat (n : ℕ) : interp_raw (fromNat n) = n := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    match n with
    | 0 => simp only [fromNat, interp_raw]
    | 1 => simp only [fromNat, interp_raw, interp_nil]
    | (m+2) =>

      apply Nat.eq_of_factorization_eq
      . simp only [fromNat, Nat.succ_eq_add_one, interp_raw, ne_eq, zero_lt_iff.mp interp_list_gt_zero, not_false_eq_true]
      . simp only [ne_eq, Nat.add_eq_zero_iff, OfNat.ofNat_ne_zero, and_false, not_false_eq_true]
      . intro p

        by_cases hp : Nat.Prime p
        · obtain ⟨i, hi⟩ := prime_index hp
          rw [hi]

          -- Apply  the Bridge Lemma (factorization_interp_list)
          simp only [fromNat, interp_raw]
          rw [← Nat.zero_add i, factorization_interp_list 0 i]
          rw [Nat.zero_add]

          -- Now we evaluate `(get xs i).interp_raw`
          simp only [Nat.succ_eq_add_one, Nat.add_assoc, one_add_one_eq_two]
          if hi_bound : i < (m+2) then
            simp only [get]
            rw [List.getD_eq_getElem _ zero (by simp [hi_bound])]
            simp
            apply ih
            apply Nat.factorization_lt
            linarith

          else

            simp only [get]
            rw [List.getD_eq_default _ zero (by simp only [List.length_map, List.length_range]; linarith)]
            simp only [interp_raw]
            apply Eq.symm
            apply Nat.factorization_eq_zero_of_lt
            grind only [!prime_index_lt]

        · -- If p is not prime, both factorizations are 0
          rw [Nat.factorization_eq_zero_of_not_prime _ hp]
          rw [Nat.factorization_eq_zero_of_not_prime _ hp]



theorem interp_surj {n : ℕ }: ∃ x : RawProd, interp_raw x = n := by
  use fromNat n
  exact interp_fromNat n

end RawProd

namespace QProd


theorem interp_bijective : Function.Bijective interp := by
  constructor
  . unfold Function.Injective
    apply Quotient.ind₂
    intro x y h
    simp only [interp, Quotient.lift_mk] at h
    apply Quotient.sound
    apply RawProd.interp_inj
    exact h
  . unfold Function.Surjective
    intro n
    use fromNat n
    simp only [interp, fromNat]
    rw [← brak_eq_mk, Quotient.lift_mk RawProd.interp_raw @RawProd.equiv_interp_eq (RawProd.fromNat n)]
    apply RawProd.interp_fromNat
    -- this should be way easier to do automatically wtf

end QProd
