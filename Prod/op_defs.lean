import Prod.quot_defs
import Mathlib.Data.List.Basic
import Mathlib.Data.List.Induction

namespace RawProd

def prune_raw : (x : RawProd ) → (y : RawProd) →  RawProd
  | zero, _        => zero
  | _, zero        => zero
  | cons xs, cons ys => cons (List.zipWith prune_raw xs ys)
termination_by x y => size x + size y
decreasing_by
  simp [size]
  sorry

@[simp]
lemma zero_prune_eq_zero (x : RawProd) : prune_raw zero x = zero := by simp only [prune_raw]

@[simp]
lemma prune_zero_eq_zero (x : RawProd) : prune_raw x zero = zero := by
  cases x <;> simp [prune_raw]



@[simp]
lemma prune_nil_eq_nil (xs : List RawProd) : prune_raw (cons xs) (cons []) = cons [] := by
  -- how does simp not work?
    simp only [prune_raw, List.zipWith_nil_right]

@[simp]
lemma nil_prune_eq_nil (xs : List RawProd) : prune_raw (cons []) (cons xs) = cons [] := by
  cases xs <;> simp only [prune_raw, List.zipWith_nil_left]




/-- compatibility: if `x ≈ x'` and `y ≈ y'` then `prune_raw x y ≈ prune_raw x' y'`.
    This is the only lemma needed to lift to the quotient. -/
theorem prune_raw_respects_equiv {x x' y y' : RawProd} (hx : x.equiv x') (hy : y.equiv y') :
  (prune_raw x y).equiv (prune_raw x' y') := by
  have hnx := equiv_normalize_eq x x' hx
  have hny := equiv_normalize_eq y y' hy
  simp [equiv]
  sorry




  -- helper: membership of trim implies membership of the original list
lemma mem_trim_subset {l : List RawProd} {a : RawProd} (h : a ∈ trim l) : a ∈ l := by
  have hsub : trim l <+: l := by simp only [trim, List.rdropWhile_prefix]
  apply List.IsPrefix.subset hsub
  exact h




theorem prune_raw_idem (x : RawProd) : prune_raw x x = x := by
  induction x using RawProd.induction with
  | h_zero => apply prune_zero_eq_zero
  | h_cons xs ih =>
    induction xs with
    | nil => apply prune_nil_eq_nil
    | cons y ys ihy =>
      simp_all only [List.mem_cons, or_true, implies_true, prune_raw, List.zipWith_self, cons.injEq,
        forall_const, forall_eq_or_imp, List.map_cons]


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
