import Prod.quot_defs4
import Mathlib.Data.List.Induction

namespace RawProd

/-- private structural core used only to justify termination. -/
private def prune_raw_core : RawProd → RawProd → RawProd
| RawProd.zero, _ => RawProd.zero
| _, RawProd.zero => RawProd.zero
| RawProd.cons xs, RawProd.cons ys =>
  match xs, ys with
  | [], _ => RawProd.cons []
  | _, [] => RawProd.cons []
  | x :: xx, y :: yy =>
    --RawProd.cons ((prune_raw_core x y) :: List.map (Function.uncurry prune_raw_core) (List.zip xx yy))
    RawProd.cons (List.zipWith prune_raw_core xs ys)

termination_by x y => size x + size y

decreasing_by
  simp [size]
  --apply Nat.lt_add_of_pos_right
  --apply Nat.succ_pos
  sorry

/-- the single public `prune_raw` that always returns a normalized representative -/
def prune_raw (x y : RawProd) : RawProd :=
  normalize (prune_raw_core (normalize x) (normalize y))

/-- compatibility: if `x ≈ x'` and `y ≈ y'` then `prune_raw x y ≈ prune_raw x' y'`.
    This is the only lemma needed to lift to the quotient. -/
theorem prune_raw_respects_equiv {x x' y y' : RawProd} (hx : x.equiv x') (hy : y.equiv y') :
  (prune_raw x y).equiv (prune_raw x' y') := by
  have hnx := equiv_normalize_eq x x' hx
  have hny := equiv_normalize_eq y y' hy
  simp [prune_raw, hnx, hny, equiv_refl]


  -- helper: membership of trim implies membership of the original list
theorem mem_trim_subset {l : List RawProd} {a : RawProd} (h : a ∈ trim l) : a ∈ l := by
sorry

theorem children_normalized_of_parent_normalized {xs : List RawProd}
  (hparent : normalize (RawProd.cons xs) = RawProd.cons xs) :
  ∀ x ∈ xs, normalize x = x := by
  -- unfold what normalize (cons xs) is and use trim/map reasoning
  have : trim (List.map normalize xs) = xs := by
    -- normalize (cons xs) = cons (trim (map normalize xs))
    -- so equality of conses gives equality of their list arguments
    simp [normalize] at hparent
    exact hparent
  intro a ha
  -- a ∈ xs = a ∈ trim (map normalize xs)
  have a_in_trim : a ∈ trim (List.map normalize xs) := by
    rwa [←this] at ha
  -- from membership in trim(list) get membership in the mapped list
  have a_in_norm : a ∈ List.map normalize xs := by
    exact mem_trim_subset a_in_trim
  -- hence there exists orig ∈ xs with a = normalize orig
  rcases List.mem_map.1 a_in_norm with ⟨orig, orig_in_xs, rfl⟩

  apply RawProd.normalize_idem


-- couple of list lemmas
--lemma asdf : asdf List.zip_cons_cons

/-- Core lemma: if `x` is normalized then `prune_raw_core x x = x`. We prove by well-founded
    induction on `size` to mirror the structural recursion on `RawProd`. -/
theorem prune_raw_core_idem_of_normalized :
  ∀ x, normalize x = x → prune_raw_core x x = x := by
  intro x hx
  induction x using RawProd.induction with
  | h_zero => simp [prune_raw_core]
  | h_cons xs ih =>
    -- handle empty list and non-empty list separately
    cases xs with
    | nil => simp [prune_raw_core]
    | cons x1 xs' =>
      -- computation by definition of prune_raw_core
      simp [prune_raw_core]
      -- we need to show: (prune_raw_core x1 x1) :: List.map (uncurry prune_raw_core) (List.zip xs' xs') = x1 :: xs'
      -- i.e. head idempotent and tail pointwise idempotent
      -- show head idempotent using IH: size decreases


      have head_eq : prune_raw_core x1 x1 = x1 := by
        have x1_in_list : x1 ∈ x1 :: xs' := List.mem_cons_self
        -- need normalize x1 = x1; this follows because parent is normalized
        have child_norm : normalize x1 = x1 := by
          have children_norm := children_normalized_of_parent_normalized hx
          exact children_norm x1 x1_in_list
        apply ih x1 x1_in_list child_norm


      -- tail: prove by list induction that each zipped pair reduces to the same tail element
      have tail_eq : List.map (fun a ↦ prune_raw_core a a) xs' = xs' := by
        induction xs' using  List.reverseRecOn with
        | nil => simp [List.map]
        | append_singleton ys y ih_list =>


          have y_in_list : y ∈ x1 :: (ys ++ [y]) := by simp [List.mem_cons]

          have child_norm_y : normalize y = y := by
            have children_norm := children_normalized_of_parent_normalized hx
            exact children_norm y y_in_list
          have rec_y : prune_raw_core y y = y := ih y y_in_list child_norm_y
          have rec_ys : List.map (fun a ↦ prune_raw_core a a) ys = ys := --ih_list hx
            (by

              have ih_list_pre1 : ∀ x ∈ x1 :: ys, x.normalize = x → prune_raw_core x x = x := by
                intro z iz
                apply ih
                simp only [List.mem_cons] at ⊢ iz
                -- now got:
                -- iz : z = x1 ∨ z ∈ ys
                -- ⊢ z = x1 ∨ z = y ∨ z ∈ ys
                cases iz with
                | inl hl => left; exact hl
                | inr hr => right; simp [List.mem_cons]; left; exact hr


              have ih_list_pre2 : (cons (x1 :: ys)).normalize = cons (x1 :: ys) := by
                --hx : (cons (x1 :: (ys ++ [y]))).normalize = cons (x1 :: (ys ++ [y]))
                --WTS (cons (x1 :: ys)).normalize = cons (x1 :: ys)
                simp [normalize] at hx ⊢

                have hx2 : trim (x1.normalize :: (List.map normalize ys)) ++ [y] = (x1 :: ys) ++ [y] := by
                  simp [child_norm_y] at hx
                  simp_all [trim_append_zero, map_normalize_trim_of_fixed]
                  sorry
                  -- want a lemma that trim(xs ++ [y]) = xs ++ [y] -> trim xs ++ [y] = xs ++ [y]
                rw [List.append_left_inj] at hx2
                exact hx2

              exact ih_list ih_list_pre1 ih_list_pre2
            )

          simp [rec_y, rec_ys]
      -- combine head and tail equalities
      simp [head_eq, tail_eq]



/-- Public idempotency of prune_raw: prune_raw x x = normalize (prune_raw_core (normalize x) (normalize x))
    and by the core lemma above we get normalized representative equals normalize x; then use normalize_idem. -/
theorem prune_raw_idem (x : RawProd) : (prune_raw x x) ≈ x := by
  -- let n = normalize x (canonical representative)
  let n := normalize x
  have hn_norm : normalize n = n := by rw [normalize_idem]
  -- use core lemma with normalized representative `n`
  have core_eq : prune_raw_core n n = n := prune_raw_core_idem_of_normalized n hn_norm
  -- compute prune_raw x x and reduce
  have : prune_raw x x = normalize (prune_raw_core n n) := rfl
  calc
    prune_raw x x = normalize (prune_raw_core n n) := by rfl
    _ = normalize n := by rw [core_eq]
    _ = n := by rw [normalize_idem]
    _ ≈ x := by
      -- we use the lemma that normalized representative is equivalent to original:
      -- `equiv_of_normalize : normalize x ≈ x` — replace with your lemma name if different.
      subst n
      exact equiv_of_normalize x


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
  simp [prune_raw, normalize_zero_eq_zero, prune_raw_core, zero_eq_zero]


/-- `prune` is idempotent on `QProd`: prune q q = q.
    This follows immediately from `RawProd.prune_raw_idem` + `Quotient.sound`. -/
theorem prune_idem : ∀ q, prune q q = q := by
  apply Quotient.ind
  intro x
  apply Quotient.sound (RawProd.prune_raw_idem x)



end QProd
