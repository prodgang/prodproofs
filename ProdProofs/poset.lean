
import ProdProofs.defs

namespace ProdProofs

lemma prod_leq_refl (p: prod_num) : prod_leq p p := by
  induction p using prod_num.induction_on
  case hp0 =>
    simp [prod_leq]
  case hpli ps ih =>
    cases ps
    case nil =>
      simp [prod_leq]
    case cons head tail =>
      simp [prod_leq]
      constructor
      · exact ih head (List.mem_cons_self head tail)
      · have htail : sizeOf tail < sizeOf (head::tail) := by simp_wf
        exact prod_leq_refl (prod_num.pli tail)
termination_by p
decreasing_by
  rename_i orig h t ps ho
  simp [sizeOf]
  sorry

lemma prod_leq_trans (p q r : prod_num) : prod_leq p q → prod_leq q r → prod_leq p r := by
  induction p using prod_num.induction_on
  case hp0 =>
    -- Base case: `p = p0`, so `prod_leq p0 _` is always `True`.
    simp [prod_leq]
  case hpli ps ih =>
    -- Inductive step for `p = pli ps`.
    intros hpq hqr
    induction q using prod_num.induction_on
    case hp0 =>
      -- If `q = p0`, this is absurd because `hpq` would be `False`.
      absurd hpq
      simp [prod_leq]
    case hpli qs ih_q =>
      -- Inductive step for `q = pli qs`.
      induction r using prod_num.induction_on
      case hp0 =>
        -- If `r = p0`, this is absurd because `hqr` would be `False`.
        absurd hqr
        simp [prod_leq]
      case hpli rs ih_r =>
        -- Inductive step for `r = pli rs`.
        -- Expand the definitions of `prod_leq` for all three.
        rw [prod_leq.eq_def] at hpq hqr ⊢
        simp
        cases ps with
        | nil =>
          -- If `ps` is empty, `prod_leq (pli []) _` is always `True`.
          exact True.intro
        | cons p ps_tail =>
          cases qs with
          | nil =>
            -- If `qs` is empty, `prod_leq (pli ps) (pli qs)` is determined by `prod_leq (pli ps_tail) (pli [])`.
            absurd hpq
            simp [prod_leq]
          | cons q qs_tail =>
            cases rs with
            | nil =>
              -- If `rs` is empty, this is absurd because `prod_leq _ (pli [])` is `False`.
              simp [prod_leq] at hqr
              contradiction
            | cons r rs_tail =>
              -- Now we have `ps = p :: ps_tail`, `qs = q :: qs_tail`, and `rs = r :: rs_tail`.
              -- Split `prod_leq` into element-wise comparisons and apply the IHs.
              simp [prod_leq] at hpq hqr ⊢
              exact ⟨
                ih p q r hpq.left hqr.left,       -- Apply IH on the first elements.
                ih ps_tail qs_tail rs_tail hpq.right hqr.right -- Apply IH on the tails.
              ⟩


lemma prod_leq_cons_then_zero (ps : List prod_num) (hleq: prod_leq (prod_num.pli ps) (prod_num.pli [])) :  prod_num.pli [] = prod_num.pli ps := by
  -- some padding shit
  sorry

lemma prod_leq_antisymm (p q : prod_num) : prod_leq p q → prod_leq q p → p = q := by
  induction p using prod_num.induction_on
  case hp0 =>
    intros h1 h2
    induction q using prod_num.induction_on
    case hp0 => simp
    case hpli => absurd h2; simp [prod_leq]
  case hpli ps hp =>
    induction q using prod_num.induction_on
    intros h1 h2
    case hp0 => absurd h1; simp [prod_leq]
    case hpli qs hq =>
      intros h1 h2
      --rw [prod_leq.eq_def] at h1 h2
      --simp at h1 h2
      cases ps
      case nil =>
        cases qs
        case nil => simp
        case cons h t => exact prod_leq_cons_then_zero (h::t) h2
      case cons hps tps =>
        cases qs
        case nil => simp [← prod_leq_cons_then_zero (hps::tps) h1]
        case cons hqs tqs => sorry -- the only case that actually counts...

theorem prod_leq_trans_2 (x y z : prod_num) : prod_leq x y → prod_leq y z → prod_leq x z
| .p0, _, _ => by simp
| .pli xs, .p0, _ => by simp
| .pli xs, .pli ys, .p0 => by simp
| .pli xs, .pli ys, .pli zs =>
  have hxy : ∀ i, i < xs.length → prod_leq (xs.get i) (ys.get i), from hxy,
  have hyz : ∀ i, i < ys.length → prod_leq (ys.get i) (zs.get i), from hyz,
  apply and.intro;
  { apply prod_leq_trans_2, assumption },
  { apply prod_leq_trans_2, assumption }


end ProdProofs
