import Prod.quot_defs
-- import Mathlib.Data.List.Basic
-- import Mathlib.Data.List.Induction

namespace RawProd

def prune_raw : (RawProd ) → (RawProd) →  RawProd
  | zero, _        => zero
  | _, zero        => zero
  | brak xs, brak ys => brak (List.zipWith prune_raw xs ys)
termination_by x y => size x + size y
decreasing_by
  simp [size]
  sorry


infixl:70 " ⊓ " => prune_raw


@[simp]
lemma zero_prune_eq_zero (x : RawProd) : zero ⊓ x = zero := by simp only [prune_raw]

@[simp]
lemma prune_zero_eq_zero (x : RawProd) : x ⊓ zero = zero := by
  cases x <;> simp [prune_raw]



@[simp]
lemma brak_prune_nil_eq_nil {xs : List RawProd} : (brak xs) ⊓ (brak []) = brak [] := by
  -- how does simp not work?
    simp only [prune_raw, List.zipWith_nil_right]

@[simp]
lemma brak_nil_prune_eq_nil (xs : List RawProd) : (brak []) ⊓ (brak xs) = brak [] := by
  cases xs <;> simp only [prune_raw, List.zipWith_nil_left]

@[simp]
lemma prune_nil_nz_eq_nil (x : RawProd) (hnz: x ≠ zero) : x ⊓ (brak []) = brak [] := by
    cases x <;> simp only [prune_raw, List.zipWith_nil_right]
    contradiction

@[simp]
lemma prune_nil_eq_nil (xs : List RawProd) : (brak xs) ⊓ (brak []) = brak [] := by
    cases xs <;> simp only [prune_raw, List.zipWith_nil_right]


@[simp]
lemma nil_prune_nz_eq_nil (x : RawProd) (hnx : x ≠ zero) : (brak []) ⊓ x = brak [] := by
  cases x <;> simp only [prune_raw, List.zipWith_nil_left]
  contradiction

@[simp]
lemma nil_prune_brak_eq_nil (xs : List RawProd)  : (brak []) ⊓ (brak xs) = brak [] := by
  cases xs <;> simp only [prune_raw, List.zipWith_nil_left]

lemma brak_prune_brak_neq_zero (xs ys : List RawProd) : (brak xs) ⊓ (brak ys) ≠ zero := by
  simp only [prune_raw, ne_eq, reduceCtorEq, not_false_eq_true]

lemma brak_prune_brak_eq_brak (xs ys : List RawProd) : ∃ zs, (brak xs) ⊓ (brak ys) = (brak zs) := by sorry


lemma cons_prune_cons {xs ys : List RawProd} {x y : RawProd} : (brak (x::xs)) ⊓ (brak (y::ys)) = brak ((x ⊓ y)::(List.zipWith prune_raw xs ys)) := by
  simp only [prune_raw, List.zipWith_cons_cons]


lemma allzero_prune_eq_allzero {xs ys : List RawProd} (haz : allzero xs) : ((brak xs) ⊓ (brak ys)) = brak (List.replicate (max xs.length ys.length) zero) := by
  --needs to be cleaner
  sorry

  -- helper: membership of trim implies membership of the original list
-- lemma mem_trim_subset {l : List RawProd} {a : RawProd} (h : a ∈ trim l) : a ∈ l := by
--   have hsub : trim l <+: l := by simp only [trim, List.rdropWhile_prefix]
--   apply List.IsPrefix.subset hsub
--   exact h


/-- compatibility: if `x ≈ x'` and `y ≈ y'` then `prune_raw x y ≈ prune_raw x' y'`.
    This is the only lemma needed to lift to the quotient. -/
-- theorem prune_raw_respects_equiv_cases {x x' y y' : RawProd} (hx : x.equiv x') (hy : y.equiv y') :
--   (x ⊓ y).equiv (x' ⊓ y') := by
--   -- have hnx := equiv_normalize_eq x x' hx
--   -- have hny := equiv_normalize_eq y y' hy
--   --simp [equiv]
--   cases x
--   case zero =>
--     have hx'z : x' = zero := by simp only [equiv, normalize_zero_eq_zero] at hx; exact zero_eq_normalize_eq_zero hx
--     simp_all only [normalize_zero_eq_zero, zero_eq_normalize_eq_zero, zero_prune_eq_zero]
--   case brak xs =>
--     cases y
--     case zero =>
--       have hy'z : y' = zero := by simp [equiv, normalize_zero_eq_zero] at hy; exact zero_eq_normalize_eq_zero hy
--       simp_all only [normalize_zero_eq_zero, zero_eq_normalize_eq_zero, prune_zero_eq_zero]
--     case brak ys =>
--       cases x'
--       case zero => absurd hx; exact not_brak_equiv_zero xs
--       case brak xs' =>
--         cases y'
--         case zero => absurd hy; exact not_brak_equiv_zero ys
--         case brak ys' =>
--           simp_all [equiv, normalize]
--           sorry -- induction on all lists?

theorem prune_raw_idem (x : RawProd) : x ⊓ x = x := by
  induction x using RawProd.induction_list with
  | h_zero => apply prune_zero_eq_zero
  | h_nil => apply brak_prune_nil_eq_nil
  | h_cons xs ih =>
    simp_all only [prune_raw, List.zipWith_self, brak.injEq, List.map_cons]


theorem prune_raw_comm (x y : RawProd ): x ⊓ y = y ⊓ x := by
  revert x y
  apply RawProd.induction_list₂
  case h_zero_left => simp only [zero_prune_eq_zero, prune_zero_eq_zero, implies_true]
  case h_zero_right => simp only [prune_zero_eq_zero, zero_prune_eq_zero, implies_true]
  case h_nil_left => simp only [ne_eq, brak_neq_zero, not_false_eq_true, nil_prune_nz_eq_nil, prune_nil_eq_nil, implies_true]
  case h_nil_right => simp only [ne_eq, brak_neq_zero, not_false_eq_true, prune_nil_nz_eq_nil, nil_prune_nz_eq_nil, implies_true]
  case h_cons_cons =>
    intro x y xs ys hx hxs
    simp only [prune_raw, List.zipWith_cons_cons, brak.injEq, List.cons.injEq] at hxs ⊢
    exact ⟨hx, hxs⟩





theorem prune_raw_assoc {x y z : RawProd }: x ⊓ (y ⊓ z) = (x ⊓ y) ⊓ z := by
  revert x y z
  apply RawProd.induction_list₃
  case h_zero_left => simp only [zero_prune_eq_zero, implies_true];
  case h_zero_mid => simp only [zero_prune_eq_zero, prune_zero_eq_zero, implies_true]
  case h_zero_right => simp only [prune_zero_eq_zero, implies_true]
  case h_nil_left => simp only [ne_eq, brak_prune_brak_neq_zero, not_false_eq_true, nil_prune_nz_eq_nil, brak_neq_zero, implies_true]
  case h_nil_mid => simp only [brak_nil_prune_eq_nil, brak_prune_nil_eq_nil, implies_true]
  case h_nil_right => simp only [prune_raw, List.zipWith_nil_right, implies_true]
  case h_cons_cons_cons =>
    intros x y z xs ys zs hx hxs
    simp only [prune_raw, brak.injEq, List.zipWith_cons_cons, List.cons.injEq] at ⊢ hxs
    exact ⟨hx, hxs⟩


-- helper to cover all nil cases below
lemma prune_raw_trim_equiv {xs ys : List RawProd} : (brak []).equiv (brak xs) → (brak []).equiv (brak xs ⊓ brak ys) := by
  intro h1
  have haz : allzero xs := by exact nil_equiv_brak_iff_allzero.mp h1
  simp only [allzero_prune_eq_allzero haz]
  simp only [nil_equiv_brak_iff_allzero, allzero, List.length_replicate]

theorem prune_raw_respects_equiv {x x' y y' : RawProd} (hx : x.equiv x') (hy : y.equiv y') : (x ⊓ y).equiv (x' ⊓ y') := by
  revert x x' y y'
  apply induction_list₄
  case h_zero1 => intro x y z h1 h2; rw [equiv_zero_eq_zero h1]; simp only [zero_prune_eq_zero]; rfl
  case h_zero2 => intro x y z h1 h2; rw [zero_equiv_eq_zero h1]; simp only [zero_prune_eq_zero]; rfl
  case h_zero3 => intro x y z h1 h2; rw [equiv_zero_eq_zero h2]; simp only [prune_zero_eq_zero]; rfl
  case h_zero4 => intro x y z h1 h2; rw [zero_equiv_eq_zero h2]; simp only [prune_zero_eq_zero]; rfl
  case h_nil1 => intros; simp only [ne_eq, brak_neq_zero, not_false_eq_true, nil_prune_nz_eq_nil]; apply prune_raw_trim_equiv; assumption;
  case h_nil2 => intros; simp only [ne_eq, brak_neq_zero, not_false_eq_true, nil_prune_nz_eq_nil]; apply equiv_symm; apply prune_raw_trim_equiv; apply equiv_symm; assumption;
  case h_nil3 => intros ws xs zs h1 h2; rw [prune_raw_comm (brak xs) (brak zs)]; simp only [ne_eq, brak_neq_zero, not_false_eq_true, prune_nil_nz_eq_nil]; apply prune_raw_trim_equiv; exact h2
  case h_nil4 => intros ws xs zs h1 h2; rw [prune_raw_comm (brak ws) (brak zs)]; simp only [ne_eq, brak_neq_zero, not_false_eq_true, prune_nil_nz_eq_nil]; apply equiv_symm; apply prune_raw_trim_equiv; apply equiv_symm; exact h2
  case h_cons_cons_cons_cons =>
    intro w x y z ws xs ys zs h hs h1 h2
    simp only [cons_prune_cons]
    obtain ⟨h1h, h1t⟩ := cons_equiv_cons_iff.mpr h1
    obtain ⟨h2h, h2t⟩ := cons_equiv_cons_iff.mpr h2
    apply cons_equiv_cons_iff.mp; constructor
    . apply h; exact h1h; exact h2h
    . simp [prune_raw] at hs
      apply hs; exact h1t; exact h2t




end RawProd

namespace QProd

open RawProd

/-- Lift the single `prune_raw` to `QProd`. -/
def prune (x y : QProd) : QProd :=
  Quotient.liftOn₂ x y (fun a b => mk (RawProd.prune_raw a b)) fun _ _ _ _ hx hy =>
    Quotient.sound (RawProd.prune_raw_respects_equiv hx hy)


infixl:70 " ⊓ " => prune


/-- compute on `mk`ed representatives -/
lemma prune_mk_mk (x y : RawProd) : (mk x) ⊓ (mk y) = mk (x ⊓ y) := rfl

/-- basic simplification: prune zero zero = zero -/
lemma zero_prune_zero_eq_zero : zero ⊓ zero = zero := by
  change prune (mk RawProd.zero) (mk RawProd.zero) = mk RawProd.zero
  rw [prune_mk_mk]
  simp only [prune_zero_eq_zero, mk_zero_eq_zero]



theorem prune_idem {q : QProd }: q ⊓ q = q := by
  revert q
  apply Quotient.ind
  intro x
  apply Quotient.sound
  rw [prune_raw_idem]
  rfl


theorem prune_comm {x y : QProd } : x ⊓ y = y ⊓ x := by
  revert x y
  apply Quotient.ind₂
  intro x y
  apply Quotient.sound
  rw [prune_raw_comm]
  rfl

theorem prune_assoc {x y z : QProd} : x ⊓ (y ⊓ z) = (x ⊓ y) ⊓ z := by
  refine Quotient.inductionOn₃ x y z ?_
  intro a b c
  apply Quotient.sound
  rw [prune_raw_assoc]
  rfl



end QProd
