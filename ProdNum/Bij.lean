/-
Copyright (c) 2024 Edwin Agnew. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Edwin Agnew
-/
import ProdNum.Interp
import ProdNum.QuotDefs
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.Nat.Prime.Nth
import Mathlib.NumberTheory.PrimeCounting
import Mathlib.Tactic.Linarith.Frontend

/-!
# Productive Numbers — Bijectivity of Interpretation

Proves that `ProdNum.interp : ProdNum → ℕ` is a bijection.

## Main results

- `PreProdNum.interp_inj`: `interp x = interp y → x.equiv y`
- `PreProdNum.interp_fromNat`: `interp (fromNat n) = n`
- `ProdNum.interp_bijective`: `Function.Bijective ProdNum.interp`
-/

namespace PreProdNum

lemma brak_equiv_elementwise {xs ys : List PreProdNum}
    (h : ∀ i, (get xs i).equiv (get ys i)) : (brak xs).equiv (brak ys) := by
  induction xs generalizing ys with
  | nil =>
    simp only [equiv, normalize, List.map_nil, brak.injEq]
    simp only [trim, List.rdropWhile_nil, List.nil_eq, List.rdropWhile_eq_nil_iff, List.mem_map, beq_iff_eq, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂]
    intro y hy
    suffices hyz : y = zero by rw [hyz, normalize_zero]
    obtain ⟨n, hn⟩ := (List.mem_iff_get.mp hy)
    specialize h n
    simp only [get, List.getD_nil] at h
    apply equiv_zero_eq_zero at h
    subst hn
    simp_all only [List.getD_eq_getElem?_getD, Fin.is_lt, getElem?_pos, Option.getD_some, List.get_eq_getElem]

  | cons x xs ih =>
    cases ys with
    | nil =>
      simp only [equiv, normalize, List.map_nil, brak.injEq]
      simp only [trim, List.rdropWhile_nil, List.rdropWhile_eq_nil_iff, List.mem_map, beq_iff_eq, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂]
      intro x hx
      suffices hxz : x = zero by rw [hxz, normalize_zero]
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

theorem interp_inj {x y : PreProdNum} : interp x = interp y → x.equiv y := by
  revert y
  induction x using induction with
  | h_zero =>
    intro y h
    simp only [interp_zero] at h
    exact (interp_eq_zero_eq_zero y h.symm).symm ▸ equiv_refl zero
  | h_brak xs ih =>
    intro y h
    cases y with
    | zero =>
      simp only [interp_zero] at h
      exact (interp_eq_zero_eq_zero (brak xs) h).symm ▸ equiv_refl zero
    | brak ys =>
      have h_factors : ∀ i, interp (get xs i) = interp (get ys i) := by
        intro i
        rw [← factorization_interp_list 0 i, ← factorization_interp_list 0 i]
        simp only [Nat.zero_add]
        simp only [interp] at h
        rw [h]

      apply brak_equiv_elementwise

      intro i
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
          have y_is_zero := interp_eq_zero_eq_zero _ (h_factors).symm
          rw [y_is_zero]
          exact equiv_refl zero


lemma brak_equiv_get_equiv {xs ys : List PreProdNum}
    (h : (brak xs).equiv (brak ys)) (i : ℕ) : (get xs i).equiv (get ys i) := by
  apply interp_inj
  have heq : interp (brak xs) = interp (brak ys) := equiv_interp_eq h
  simp only [interp] at heq
  linarith [factorization_interp_list_zero (xs := xs) i, factorization_interp_list_zero (xs := ys) i,
            heq ▸ (factorization_interp_list_zero (xs := xs) i)]

/-! ### Surjectivity -/



theorem interp_fromNat (n : ℕ) : interp (fromNat n) = n := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    match n with
    | 0 => simp only [fromNat, interp]
    | 1 => simp only [fromNat, interp, interp_nil]
    | (m+2) =>

      apply Nat.eq_of_factorization_eq
      . simp only [fromNat, Nat.succ_eq_add_one, interp, ne_eq, interp_list_neq_zero, not_false_eq_true]
      . simp only [ne_eq, Nat.add_eq_zero_iff, OfNat.ofNat_ne_zero, and_false, not_false_eq_true]
      . intro p

        by_cases hp : Nat.Prime p
        · obtain ⟨i, hi⟩ := prime_index hp
          rw [hi]

          simp only [fromNat, interp]
          rw [← Nat.zero_add i, factorization_interp_list 0 i]
          rw [Nat.zero_add]
          simp only [Nat.succ_eq_add_one, Nat.add_assoc, one_add_one_eq_two]
          if hi_bound : i < (m+2) then
            simp only [get]
            rw [List.getD_eq_getElem _ zero (by simp only [List.length_map, List.length_range,
              hi_bound])]
            simp
            apply ih
            apply Nat.factorization_lt
            linarith

          else
            simp only [get]
            rw [List.getD_eq_default _ zero (by simp only [List.length_map, List.length_range]; linarith)]
            simp only [interp]
            apply Eq.symm
            apply Nat.factorization_eq_zero_of_lt
            grind only [!prime_index_lt]

        · rw [Nat.factorization_eq_zero_of_not_prime _ hp]
          rw [Nat.factorization_eq_zero_of_not_prime _ hp]



end PreProdNum

namespace ProdNum


theorem interp_bijective : Function.Bijective interp := by
  constructor
  · unfold Function.Injective
    apply Quotient.ind₂
    intro x y h
    simp only [interp, Quotient.lift_mk] at h
    exact Quotient.sound (PreProdNum.interp_inj h)
  · intro n
    refine ⟨fromNat n, ?_⟩
    show interp (mk (PreProdNum.fromNat n)) = n
    rw [interp_mk]
    exact PreProdNum.interp_fromNat n

end ProdNum
