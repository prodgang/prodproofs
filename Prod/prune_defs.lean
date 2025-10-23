import Prod.quot_defs
import Mathlib.Data.List.Basic
import Mathlib.Data.List.Induction

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
lemma brak_prune_nil_eq_nil (xs : List RawProd) : (brak xs) ⊓ (brak []) = brak [] := by
  -- how does simp not work?
    simp only [prune_raw, List.zipWith_nil_right]

@[simp]
lemma brak_nil_prune_eq_nil (xs : List RawProd) : (brak []) ⊓ (brak xs) = brak [] := by
  cases xs <;> simp only [prune_raw, List.zipWith_nil_left]

@[simp]
lemma prune_nil_eq_nil (x : RawProd) (hnz: x ≠ zero) : x ⊓ (brak []) = brak [] := by
    cases x <;> simp only [prune_raw, List.zipWith_nil_right]
    contradiction

@[simp]
lemma nil_prune_eq_nil (x : RawProd) (hnx : x ≠ zero) : (brak []) ⊓ x = brak [] := by
  cases x <;> simp only [prune_raw, List.zipWith_nil_left]
  contradiction


lemma brak_prune_brak_neq_zero (xs ys : List RawProd) : (brak xs) ⊓ (brak ys) ≠ zero := by
  simp only [prune_raw, ne_eq, reduceCtorEq, not_false_eq_true]






/-- compatibility: if `x ≈ x'` and `y ≈ y'` then `prune_raw x y ≈ prune_raw x' y'`.
    This is the only lemma needed to lift to the quotient. -/
theorem prune_raw_respects_equiv {x x' y y' : RawProd} (hx : x.equiv x') (hy : y.equiv y') :
  (x ⊓ y).equiv (x' ⊓ y') := by
  have hnx := equiv_normalize_eq x x' hx
  have hny := equiv_normalize_eq y y' hy
  simp [equiv]
  sorry




  -- helper: membership of trim implies membership of the original list
-- lemma mem_trim_subset {l : List RawProd} {a : RawProd} (h : a ∈ trim l) : a ∈ l := by
--   have hsub : trim l <+: l := by simp only [trim, List.rdropWhile_prefix]
--   apply List.IsPrefix.subset hsub
--   exact h




theorem prune_raw_idem (x : RawProd) : x ⊓ x = x := by
  induction x using RawProd.induction with
  | h_zero => apply prune_zero_eq_zero
  | h_brak xs ih =>
    induction xs with
    | nil => apply brak_prune_nil_eq_nil
    | cons y ys ihy =>
      simp_all only [List.mem_cons, or_true, implies_true, prune_raw, List.zipWith_self, brak.injEq,
        forall_const, forall_eq_or_imp, List.map_cons]


theorem prune_raw_comm : ∀ x y, x ⊓ y = y ⊓ x := by
  apply RawProd.strong_induction₂ --(prune_raw x y = prune_raw y x)
  case h_zero_left => simp only [zero_prune_eq_zero, prune_zero_eq_zero, implies_true]
  case h_zero_right => simp only [prune_zero_eq_zero, zero_prune_eq_zero, implies_true]
  case h_brak_brak =>
    intro xs ys ih
    induction xs generalizing ys with
    | nil => simp only [ne_eq, reduceCtorEq, not_false_eq_true, nil_prune_eq_nil, prune_nil_eq_nil]
    | cons z zs ihz => -- want double induction instead actually or do I? double induction seems to be stronger than pairwise
      cases ys with
      | nil => simp only [ne_eq, reduceCtorEq, not_false_eq_true, prune_nil_eq_nil, nil_prune_eq_nil]
      | cons y yy =>
        simp only [prune_raw, List.zipWith_cons_cons, brak.injEq, List.cons.injEq]
        constructor
        . have hzin : z ∈ z :: zs := by simp only [List.mem_cons, true_or]
          have hyin : y ∈ y :: yy := by simp only [List.mem_cons, true_or]
          exact ih z hzin y hyin
        . simp only [prune_raw, brak.injEq] at ihz;
          have ihzs : ∀ x ∈ zs, ∀ y ∈ yy, x.prune_raw y = y.prune_raw x := by intro x hx y hyy; apply ih <;> simp only [List.mem_cons]; right; exact hx; right; exact hyy
          exact ihz yy ihzs


theorem prune_raw_assoc : ∀ x y z, x ⊓ (y ⊓ z) = (x ⊓ y) ⊓ z := by
  apply RawProd.strong_induction₃
  case h_zero_left => simp only [zero_prune_eq_zero, implies_true];
  case h_zero_mid => simp only [zero_prune_eq_zero, prune_zero_eq_zero, implies_true]
  case h_zero_right => simp only [prune_zero_eq_zero, implies_true]
  case h_brak_brak_brak =>
    intros xs ys zs ih
    induction xs generalizing ys zs with
    | nil => --brak [] ⊓ (brak ys ⊓ brak zs) = brak [] ⊓ brak ys ⊓ brak zs
      simp only [ne_eq, brak_prune_brak_neq_zero, not_false_eq_true, nil_prune_eq_nil, reduceCtorEq]
    | cons x' xx ihxx =>
      cases ys with
      | nil => --brak (x' :: xx) ⊓ (brak [] ⊓ brak zs) = brak (x' :: xx) ⊓ brak [] ⊓ brak zs
        simp only [ne_eq, reduceCtorEq, not_false_eq_true, nil_prune_eq_nil, prune_nil_eq_nil]
      | cons y yy =>
        simp only [prune_raw, List.zipWith_cons_cons, brak.injEq]
        cases zs with
        | nil => simp only [List.zipWith_nil_right]
        | cons z zz =>
          simp_all only [List.mem_cons, or_true, prune_raw, brak.injEq, forall_eq_or_imp, List.zipWith_cons_cons, implies_true]
          -- wouldnt bother inspecting tbh




lemma prune_raw_idem_equiv (x : RawProd) : prune_raw x x ≈ x := by
  rw [prune_raw_idem]



end RawProd

namespace QProd

open RawProd

/-- Lift the single `prune_raw` to `QProd`. -/
def prune (x y : QProd) : QProd :=
  Quotient.liftOn₂ x y (fun a b => mk (RawProd.prune_raw a b)) fun _ _ _ _ hx hy =>
    Quotient.sound (RawProd.prune_raw_respects_equiv hx hy)

/-- compute on `mk`ed representatives -/
lemma prune_mk_mk (x y : RawProd) : prune (mk x) (mk y) = mk (RawProd.prune_raw x y) := rfl

/-- basic simplification: prune zero zero = zero -/
lemma zero_prune_zero_eq_zero : prune zero zero = zero := by
  change prune (mk RawProd.zero) (mk RawProd.zero) = mk RawProd.zero
  rw [prune_mk_mk]
  simp only [prune_zero_eq_zero, zero_eq_zero]



/-- `prune` is idempotent on `QProd`: prune q q = q.
    This follows immediately from `RawProd.prune_raw_idem` + `Quotient.sound`. -/
theorem prune_idem : ∀ q, prune q q = q := by
  apply Quotient.ind
  intro x
  apply Quotient.sound (RawProd.prune_raw_idem_equiv x)



end QProd
