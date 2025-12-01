import Prod.prune_basic
import Prod.poset


namespace RawProd


-- has to be equiv because [0, 0] ⊑ [] but [0, 0] ⊓ [] = []
--theorem pleq_implies_prune : ∀ x y, x ⊑ y →  (x ⊓ y).equiv x := by
  -- apply RawProd.strong_induction₂
  -- case h_zero_left => intro _ _ ; rw [zero_prune_eq_zero]; rfl
  -- case h_zero_right => intro x hx; simp only [prune_zero_eq_zero]; simp only [(pleq_zero_eq_zero hx)]; rfl
  -- case h_brak_brak =>
  --   intro xs ys ih hleq
  --   induction xs generalizing ys with
  --   | nil => rw [nil_prune_eq_nil]; rfl; exact brak_neq_zero
  --   | cons xh xt ihxs =>
  --     induction ys with
  --     | nil => -- use brak xs ⊑ [] to get allzero xs and then...
  --       have haz := brak_pleq_nil_eq_replicate_zero hleq
  --       rw [brak_prune_nil_eq_nil, haz]
  --       simp [equiv, normalize, trim_nil_eq_nil]
  --       apply trim_eq_nil_iff.mpr
  --       simp only [allzero, List.length_replicate]
  --     | cons yh yt ihys =>
  --       --apply ihys xh ihxs hleq -- ihxs doesnt get xh
  --       --simp [equiv, ]
  --       --apply ihys --blimy
  --       -- simp [cons_prune_cons]
  --       -- apply cons_equiv_cons
  --       -- . apply ih <;> simp [List.mem_cons]
  --       --   sorry
  --       -- . sorry
  --       simp_all [cons_prune_cons]
  --       apply cons_equiv_cons
  --       . sorry
  --       . simp

-- uses nicer induction
theorem pleq_implies_prune : ∀ x y, x ⊑ y →  (x ⊓ y).equiv x := by
  apply RawProd.strong_list_induction₂
  case h_zero_left => intro _ _ ; rw [zero_prune_eq_zero]; rfl
  case h_zero_right => intro x hx; simp only [prune_zero_eq_zero]; simp only [(pleq_zero_eq_zero hx)]; rfl
  case h_nil_left => intro _ _; rw [nil_prune_eq_nil]; rfl; exact brak_neq_zero
  case h_nil_right =>
     -- use brak xs ⊑ [] to get allzero xs and then...
    intro xs hleq
    have haz := brak_pleq_nil_eq_replicate_zero hleq
    rw [brak_prune_nil_eq_nil, haz]
    simp [equiv, normalize, trim_nil_eq_nil]
    apply trim_eq_nil_iff.mpr
    simp only [allzero, List.length_replicate]
  case h_cons_cons =>
    intro xh yh xt yt ih ht hcons
    simp [cons_prune_cons]
    apply cons_equiv_cons
    . apply ih
      exact (cons_pleq_cons_iff.mp hcons).1
    . simp only [prune_raw] at ht
      apply ht
      exact (cons_pleq_cons_iff.mp hcons).2



theorem prune_implies_pleq : ∀ x y, (x ⊓ y).equiv x → x ⊑ y := by
  apply RawProd.strong_list_induction₂
  case h_zero_left => intro _ _ ; exact zero_pleq
  case h_zero_right => intro x hx; simp only [prune_zero_eq_zero, equiv, normalize] at hx; rw [← zero_eq_normalize_eq_zero hx]; exact pleq_raw_refl x
  case h_nil_left => intro _ _ ; exact nil_pleq_brak
  case h_nil_right =>
    intro xs hprune
    rw [prune_nil_eq_nil] at hprune
    have hxs_az : allzero xs := by
      simp only [equiv, normalize, trim, List.map_nil, List.rdropWhile_nil, brak.injEq, List.nil_eq, List.rdropWhile_eq_nil_iff, List.mem_map, beq_iff_eq, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂] at hprune
      simp only [allzero_iff]
      intro x hin
      have hn := hprune x hin
      exact (zero_eq_normalize_eq_zero hn.symm)
    simp [allzero] at hxs_az
    rw [hxs_az]
    simp only [replicate_zero_pleq_brak]
    simp only [ne_eq, brak_neq_zero, not_false_eq_true]
  case h_cons_cons =>
    intro xh yh xt yt hh ht hcons
    simp only [cons_prune_cons] at hcons
    obtain ⟨hl, hr⟩ := cons_equiv_cons_backwards hcons
    apply cons_pleq_cons_iff.mpr
    constructor
    . apply hh
      exact hl
    . apply ht
      simp only [prune_raw]
      exact hr




end RawProd
