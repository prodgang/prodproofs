import Prod.raw_defs
import Init.Data.List.Basic
import Mathlib.Data.List.DropRight
import Mathlib.Data.Quot

namespace RawProd

--def trim (xs : List RawProd) : List RawProd := (xs.reverse.dropWhile (· == zero)).reverse
def trim (xs : List RawProd) : List RawProd := xs.rdropWhile (. == zero)


/-- Recursively normalize a RawProd by removing trailing zeros at all levels -/
def normalize : RawProd → RawProd
  | zero => zero
  | brak xs => brak (trim (List.map normalize xs))

--@[simp]
lemma normalize_zero_eq_zero : normalize zero = zero := by simp only [normalize]

--@[simp]
lemma normalize_brak_neq_zero (xs : List RawProd) : normalize (brak xs) ≠ zero := by simp only [normalize, ne_eq, reduceCtorEq, not_false_eq_true]



--@[simp]
lemma trim_nil_eq_nil : trim [] = [] := by simp [trim]

-- @[simp] lemma trim_cons (x : RawProd) (xs : List RawProd) (hnz : x ≠ zero) : trim (x :: xs) = x :: trim xs := by
--   simp [trim]

--@[simp]
lemma trim_append_brak_eq_self (xs ys: List RawProd): trim ( xs ++  [brak ys]) = xs ++ [brak ys] := by
  simp only [trim, beq_iff_eq, reduceCtorEq, not_false_eq_true, List.rdropWhile_concat_neg]

-- The equiv definition stays the same:
-- def equiv_old (x y : RawProd) : Prop :=
--   match x, y with
--   | zero, zero => True
--   | zero, cons _ => False
--   | cons _, zero => False
--   | cons xs, cons ys => trim (List.map normalize xs) = trim (List.map normalize ys)

def equiv (x y : RawProd) : Prop :=
  normalize x = normalize y


theorem equiv_refl : ∀ x, equiv x x := by
  intro x
  cases x <;> simp [equiv]

theorem equiv_symm : ∀ x y, equiv x y → equiv y x := by
  intro x y h
  cases x <;> cases y <;> simp_all [equiv, normalize]


theorem equiv_trans : ∀ x y z, equiv x y → equiv y z → equiv x z := by
  intro x y z h1 h2
  cases x <;> cases y <;> cases z <;> simp_all only [equiv]

  /-- Setoid instance for productive numbers -/
instance : Setoid RawProd where
  r := equiv
  iseqv := ⟨equiv_refl, @equiv_symm, @equiv_trans⟩


-- Now normalize_eq_of_equiv becomes provable:
lemma equiv_normalize_eq : ∀ x y, equiv x y → normalize x = normalize y := by
  intro x y h
  cases x <;> cases y <;> simp [equiv, normalize] at h
  · rfl
  · rename_i xs ys
    simp only [normalize]
    congr 1

--@[simp]
lemma trim_idem (xs : List RawProd) : trim (trim xs) = trim xs := by
  apply List.rdropWhile_idempotent


-- auxiliary lemma: if f fixes every element of l, then map f l = l
lemma map_eq_of_fixed_blah {α : Type _} (f : α → α) (l : List α)
    (H : ∀ x ∈ l, f x = x) : (l.map f) = l := by
  induction l with
  | nil => simp
  | cons hd tl ih =>
    simp [List.map]
    have hhd : f hd = hd := H hd (by simp)
    have htl : ∀ x ∈ tl, f x = x := fun x hx => H x (by simp_all only [List.mem_cons, or_true, implies_true, forall_const, forall_eq_or_imp, true_and])
    have : tl.map f = tl := ih htl
    simp [hhd, this]


lemma append_eq_imp_eq_eq (xs ys : List RawProd) (x y : RawProd) (h1 : xs = ys) (h2: x = y) : xs.append [x] = ys.append [y] := by
  subst h2 h1
  simp_all only [List.append_eq]

lemma normalize_idem (x : RawProd) : normalize (normalize x) = normalize x := by
  induction x using RawProd.induction with
  | h_zero => simp only [normalize_zero_eq_zero]
  | h_brak xs ih =>
    induction xs using List.reverseRecOn with
    | nil => simp only [normalize, List.map_nil, trim_nil_eq_nil]
    | append_singleton xx x ihxx =>
      simp_all [normalize]
      cases x
      case zero => simp_all only [trim, normalize_zero_eq_zero, BEq.rfl, List.rdropWhile_concat_pos];
      case brak xx' =>
        simp_all only [normalize, trim_append_brak_eq_self, List.map_append, List.map_map, List.map_cons, List.map_nil]
        rw [← List.append_eq, ← List.append_eq]
        apply append_eq_imp_eq_eq
        . simp only [List.map_inj_left, Function.comp_apply]; intro a ha; apply ih; left; exact ha
        . -- could be cleaner but does the job
          have hxx : (brak xx').normalize.normalize = (brak xx').normalize := by apply ih; right; rfl
          simp only [normalize] at hxx
          exact hxx

--@[aesop safe]
lemma equiv_of_normalize (x : RawProd) : (normalize x).equiv x := by
  simp [equiv, normalize_idem]

--@[aesop unsafe 10%]
lemma brak_map_normalize (xs : List RawProd) :
     (brak (List.map normalize xs)).equiv (brak xs) := by
  simp [equiv, normalize]
  congr 1
  simp only [List.map_inj_left, Function.comp_apply, normalize_idem, implies_true]



--@[simp]
lemma trim_append_zero (xs : List RawProd) : trim (xs ++ [zero]) = trim xs := by
  induction xs with
  | nil => simp [trim]
  | cons y ys ih =>
    simp only [trim]
    apply List.rdropWhile_concat_pos (. == zero) (y::ys) zero
    rfl


--@[aesop safe]
lemma trim_length_leq (xs : List RawProd) : (trim xs).length ≤ xs.length := by
  simp [trim, List.rdropWhile]
  have h : (List.dropWhile (fun x ↦ x == zero) xs.reverse).length ≤ xs.reverse.length := by apply List.length_dropWhile_le (. == zero) xs.reverse
  have h2 : xs.length = xs.reverse.length := by simp only [List.length_reverse]
  rw [h2]
  exact h



--@[simp]
lemma trim_brak_eq_brak (xs : List RawProd) : trim [brak xs] = [brak xs] := by
  rfl

-- @[simp]
-- lemma trim_append_brak_eq_brak (xs ys : List RawProd) :  trim (xs ++ [brak ys]) = (xs ++ [brak ys]) := by
--   simp only [trim, beq_iff_eq, reduceCtorEq, not_false_eq_true, List.rdropWhile_concat_neg]


lemma trim_append_brak_neq_nil (xs ys : List RawProd) : trim (xs ++ [brak ys]) ≠ [] := by
  simp only [trim, beq_iff_eq, reduceCtorEq, not_false_eq_true, List.rdropWhile_concat_neg, ne_eq,
    List.append_eq_nil_iff, List.cons_ne_self, and_false]

def allzero (xs : List RawProd ): Prop := xs = List.replicate xs.length zero

instance decidable_allzero (xs : List RawProd) [DecidableEq RawProd] :
  Decidable (allzero xs) := by
  dsimp [allzero]
  infer_instance

/-another definition-/
lemma allzero_iff {xs : List RawProd} : allzero xs ↔ ∀ x ∈ xs, x = zero := by
  simp only [allzero]
  constructor
  . intro haz --x hx
    apply (List.eq_replicate_iff.mp haz).2
  . intro h
    apply List.eq_replicate_iff.mpr
    constructor
    . rfl
    . exact h


lemma not_allzero_append_zero {xs : List RawProd} (hnaz: ¬ RawProd.allzero (xs ++ [zero])) : ¬ RawProd.allzero xs := by
  simp_all [allzero]
  by_contra haz

  have hazz : List.replicate (xs.length + 1) zero = xs ++ [zero] := by
    rw [haz]
    apply List.replicate_eq_append_iff.mpr
    constructor
    simp only [List.length_replicate, List.length_cons, List.length_nil, Nat.zero_add]
    constructor
    simp only [List.length_replicate]
    simp only [List.length_cons, List.length_nil, Nat.zero_add, List.replicate_one]

  exact hnaz hazz.symm

lemma trim_eq_nil_iff {xs : List RawProd} : trim xs = [] ↔ RawProd.allzero xs := by
  induction xs using List.reverseRecOn with
  | nil => simp only [allzero, trim_nil_eq_nil, List.length_nil, List.replicate_zero]
  | append_singleton ys y ih =>
    constructor
    . intro htrim
      cases y
      . simp only [allzero, List.length_append, List.length_cons, List.length_nil, Nat.zero_add, List.replicate_succ', List.append_cancel_right_eq]
        simp only [trim_append_zero] at htrim
        exact ih.mp htrim
      . rename_i zs
        absurd htrim
        apply trim_append_brak_neq_nil
    . intro heqz
      --simp_all only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false, or_true, true_or, implies_true, iff_true, trim_append_zero]
      simp_all only [allzero, List.length_append, List.length_cons, List.length_nil, Nat.zero_add]
      simp only [List.replicate_succ', List.append_singleton_inj, trim_append_zero] at heqz ⊢
      have h :=  ih.mpr heqz.1
      rw [heqz.1] at h
      exact h

lemma allzero_cons {x : RawProd} {xs : List RawProd} (haz : allzero (x::xs)) : x = zero ∧ allzero xs := by
  simp_all [allzero]
  rw [List.replicate_succ, List.cons.injEq] at haz
  exact haz



lemma zero_eq_normalize_eq_zero {x : RawProd} (heqz : zero = x.normalize ) : x = zero := by
  cases x <;> simp_all only [normalize, normalize_zero_eq_zero, reduceCtorEq]

lemma normalize_eq_zero_eq_zero {x : RawProd} (heqz : x.normalize = zero ) : x = zero := by
  cases x <;> simp_all only [normalize, normalize_zero_eq_zero, reduceCtorEq]

 lemma not_brak_equiv_zero (xs : List RawProd) : ¬ (brak xs).equiv zero := by
  simp only [equiv, normalize_zero_eq_zero, normalize_brak_neq_zero, not_false_eq_true]

 lemma not_zero_equiv_brak (xs : List RawProd) : ¬ zero.equiv (brak xs) := by
  simp only [equiv, normalize_zero_eq_zero, normalize, reduceCtorEq, not_false_eq_true]


--@[simp]
lemma trim_replicate_zero_eq_nil {n : ℕ } : trim (List.replicate n zero) = [] := by
  induction n with
  | zero => simp only [List.replicate_zero, trim_nil_eq_nil]
  | succ n ih => simp only [trim, List.rdropWhile_eq_nil_iff, List.mem_replicate, ne_eq,
    Nat.add_eq_zero_iff, Nat.succ_ne_self, and_false, not_false_eq_true, true_and, beq_iff_eq,
    imp_self, implies_true]

lemma trim_allzero_eq_nil {xs : List RawProd } (hz : allzero xs) : trim xs = [] := by
  simp [allzero] at hz
  rw [hz]
  apply trim_replicate_zero_eq_nil






/- (hopefully) the reverse induction to end them all -/
lemma trim_cons {x : RawProd} {xs : List RawProd} : trim (x::xs) = if (allzero (x::xs)) then [] else x :: trim xs := by
  split_ifs
  case pos hpos => exact trim_eq_nil_iff.mpr hpos
  case neg hneg =>
    induction xs using List.reverseRecOn with
    | nil =>
      rw [trim_nil_eq_nil]
      simp only [trim, List.rdropWhile_eq_self_iff, ne_eq, List.cons_ne_self, not_false_eq_true, List.getLast_singleton, beq_iff_eq, forall_const]
      simp only [allzero, List.length_cons, List.length_nil, Nat.zero_add, List.replicate_one, List.cons.injEq, and_true] at hneg
      exact hneg
    | append_singleton xh xt ih =>
      rw [← List.cons_append] at ⊢ hneg
      cases xt
      . -- xt = zero
        rw [trim_append_zero, trim_append_zero]
        --rw [← List.cons_append] at hneg
        have htneg := not_allzero_append_zero hneg
        exact ih htneg
      . -- xt = brak
        simp only [trim_append_brak_eq_self]
        simp only [List.cons_append]


lemma cons_equiv_cons {x y : RawProd} {xs ys : List RawProd} :
    x.equiv y →  (brak xs).equiv (brak ys) →  (brak (x :: xs)).equiv (brak (y :: ys)) := by
    intro hxy hbb
    simp_all only [equiv, normalize, brak.injEq, List.map_cons]
    simp only [trim_cons]
    split_ifs
    . -- [] = []
      rfl
    . --xs [] ??
      rename_i hxs hys
      have hy_z : y.normalize = zero := by rw [allzero_iff] at hxs; exact hxs y.normalize (List.mem_cons_self)
      have hxs_az : allzero (List.map normalize xs) := by rw [allzero_iff] at hxs ⊢; intro x' hx'; apply hxs; apply List.mem_cons_of_mem; exact hx'   -- use hxs and some mem_cons situation
      have hys_az : allzero (List.map normalize ys) := by have hxs_nil := trim_eq_nil_iff.mpr hxs_az; rw [hxs_nil] at hbb; apply trim_eq_nil_iff.mp; exact hbb.symm -- use hx_az and hbb
      have h_fin : allzero (y.normalize :: List.map normalize ys) := by simp [allzero, List.length_cons, List.length_map] at ⊢ hys_az; rw [hy_z, hys_az]; simp only [List.replicate_succ]
      exact hys h_fin
    . -- [] ys (symm of above)
      rename_i hxs hys
      have hy_z : y.normalize = zero := by rw [allzero_iff] at hys; exact hys y.normalize (List.mem_cons_self)
      have hys_az : allzero (List.map normalize ys) := by rw [allzero_iff] at hys ⊢; intro x' hx'; apply hys; apply List.mem_cons_of_mem; exact hx'   -- use hxs and some mem_cons situation
      have hxs_az : allzero (List.map normalize xs) := by have hxs_nil := trim_eq_nil_iff.mpr hys_az; rw [hxs_nil] at hbb; apply trim_eq_nil_iff.mp; exact hbb -- use hx_az and hbb
      have h_fin : allzero (y.normalize :: List.map normalize xs) := by simp [allzero, List.length_cons, List.length_map] at ⊢ hys_az; rw [hy_z, hxs_az]; simp only [List.length_map, List.replicate_succ]
      exact hxs h_fin
    . simp only [List.cons.injEq, true_and]
      exact hbb

    -- . intro hequiv
    --   simp_all [equiv, normalize, trim_cons]
    --   split_ifs hequiv

    --   sorry


lemma cons_equiv_cons_backwards {x y : RawProd} {xs ys : List RawProd} :
    (brak (x :: xs)).equiv (brak (y :: ys)) → x.equiv y ∧ (brak xs).equiv (brak ys) := by

  intro h
  simp_all [equiv, normalize, trim_cons]
  split at h <;> split at h
  . -- [] []
    rename_i hxxs_az hyys_az
    obtain ⟨hxz, hxs_az⟩ := allzero_cons hxxs_az
    obtain ⟨hyz, hys_az⟩ := allzero_cons hyys_az
    constructor
    . rw [hxz, hyz]
    . rw [trim_allzero_eq_nil hxs_az, trim_allzero_eq_nil hys_az]
  . simp_all only [List.nil_eq, reduceCtorEq]
  . simp_all only [reduceCtorEq]
  . -- xs ys
    rename_i hxs_naz hys_naz
    simp_all only [List.cons.injEq, and_self]





end RawProd



/-- Productive numbers as a quotient type -/
def QProd := Quotient RawProd.instSetoid

namespace QProd

/-- Constructor from raw productive number -/
def mk : RawProd → QProd := Quotient.mk RawProd.instSetoid

/-- Zero element -/
def zero : QProd := mk RawProd.zero

/-- Get the normalized representative -/
def normalize : QProd → RawProd :=
  Quotient.lift RawProd.normalize RawProd.equiv_normalize_eq

def ofList (xs : List QProd) : QProd :=
  mk (RawProd.brak (xs.map normalize))

--@[simp]
lemma brak_eq_mk (x : RawProd) : ⟦x⟧ = mk x := by rfl

--@[simp]
lemma zero_eq_zero : mk RawProd.zero = QProd.zero := by rfl

lemma ofList_map_mk_eq_mk_brak (xs : List RawProd) :
    ofList (List.map mk xs) = mk (RawProd.brak xs) := by
  simp only [ofList, normalize, List.map_map]
  apply Quotient.sound
  have hl : Quotient.lift RawProd.normalize RawProd.equiv_normalize_eq ∘ mk = RawProd.normalize :=
    Quotient.lift_comp_mk _ _
  rw [hl]
  exact RawProd.brak_map_normalize xs

/-- Induction principle for QProd -/
theorem induction {P : QProd → Prop}
    (h_zero : P zero)
    (h_cons : ∀ xs : List QProd, (∀ x ∈ xs, P x) → P (ofList xs)) :
    ∀ x, P x := by
  intro x
  apply Quotient.ind
  apply RawProd.induction
  · exact h_zero
  · intro raw_xs ih_raw
    simp only [brak_eq_mk] at ih_raw ⊢
    let xs: List QProd := List.map mk raw_xs
    specialize h_cons xs
    simp only [List.mem_map, forall_exists_index, and_imp,
               forall_apply_eq_imp_iff₂, xs] at h_cons
    specialize h_cons ih_raw
    rw [ofList_map_mk_eq_mk_brak] at h_cons
    exact h_cons

end QProd
