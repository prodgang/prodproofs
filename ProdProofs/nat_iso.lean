
import Mathlib.Data.Nat.Factorization.Induction
import ProdProofs.defs

namespace ProdProofs

theorem unique_representation (n : Nat) : ∃! p : prod_num, eval_prod p = n := by
  induction n using Nat.caseStrongRecOn
  . apply ExistsUnique.intro (prod_num.p0)
    rw [eval_prod]
    sorry
  . rename_i n h
    sorry -- unique factorization stuff



lemma eval_prod_prod_factor_eq (n : Nat) : eval_prod (prod_factor n) = n := by
  induction n using Nat.recOnPrimePow
  case h0 => rw [prod_factor, eval_prod]
  case h1 => rw [prod_factor, eval_prod, eval_prod.eval_list]
  case h n p a hp h_div h0_le ih =>
    --WTS: E P (p^a * n) = p^ a * n , given E P n = n and coprime p nodiv n
    let m := p ^ a * n

    sorry

lemma eval_prod_prod_factor_eq_strong (n : Nat) : eval_prod (prod_factor n) = n := by
  induction n using Nat.strongRecOn
  rename_i n2 h
  cases n2
  . rw [prod_factor, eval_prod]
  .sorry


lemma prod_factor_eval_prod_eq (p: prod_num) : prod_factor (eval_prod p) = p := by
  induction p using prod_num.induction_on
  case hp0 =>
    rw [eval_prod, prod_factor]
  case hpli ps ih =>
    rw [eval_prod, eval_prod.eval_list.eq_def]
    split
    . simp [prod_factor]
    . rename_i _ x xs
      rw [prod_factor.eq_def]
      split
      . rename_i heq
        simp at heq
        sorry
      . sorry

def nat_prod_equiv : Nat ≃ prod_num where
  toFun := prod_factor
  invFun := eval_prod
  left_inv := eval_prod_prod_factor_eq
  right_inv := prod_factor_eval_prod_eq


end ProdProofs
