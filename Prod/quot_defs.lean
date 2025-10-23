import Prod.raw_defs
import Init.Data.List.Basic
import Mathlib.Data.List.DropRight

namespace RawProd

--def trim (xs : List RawProd) : List RawProd := (xs.reverse.dropWhile (· == zero)).reverse
def trim (xs : List RawProd) : List RawProd := xs.rdropWhile (. == zero)


/-- Recursively normalize a RawProd by removing trailing zeros at all levels -/
def normalize : RawProd → RawProd
  | zero => zero
  | brak xs => brak (trim (List.map normalize xs))

@[simp]
lemma normalize_zero_eq_zero : normalize zero = zero := by simp only [normalize]

@[simp] lemma trim_nil_eq_nil : trim [] = [] := by simp [trim]

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

@[simp]
lemma trim_idem (xs : List RawProd) : trim (trim xs) = trim xs := by
  apply List.rdropWhile_idempotent


-- auxiliary lemma: if f fixes every element of l, then map f l = l
lemma map_eq_of_fixed {α : Type _} (f : α → α) (l : List α)
    (H : ∀ x ∈ l, f x = x) : (l.map f) = l := by
  induction l with
  | nil => simp
  | cons hd tl ih =>
    simp [List.map]
    have hhd : f hd = hd := H hd (by simp)
    have htl : ∀ x ∈ tl, f x = x := fun x hx => H x (by simp_all only [List.mem_cons, or_true, implies_true, forall_const, forall_eq_or_imp, true_and])
    have : tl.map f = tl := ih htl
    simp [hhd, this]


@[aesop safe]
lemma map_normalize_trim_of_fixed {xs : List RawProd}
  (h : ∀ x ∈ xs, normalize x = x) :
  List.map normalize (trim xs) = trim xs := by
  -- right-to-left induction on xs
  induction xs using List.reverseRecOn with
  | nil =>
    -- trim [] = [], map [] = []
    simp only [trim, List.rdropWhile_nil, List.map_nil]
  | append_singleton as a ih =>
    -- h : ∀ x ∈ as ++ [a], normalize x = x
    -- build the restricted hypothesis for `as`
    let H_as : ∀ x ∈ as, normalize x = x := fun x hx =>
      -- as ⊆ as ++ [a], so use h on the appended list
      h x (List.mem_append.2 (Or.inl hx))

    -- split on whether `a` is a zero (rdropWhile drops trailing zeros)
    by_cases ha : (a == RawProd.zero)
    · -- case: a is dropped, rdropWhile (as ++ [a]) = as.rdropWhile
      have concat_rule := List.rdropWhile_concat (. == zero) as a
      have eq1 : (as ++ [a]).rdropWhile (. == zero) = as.rdropWhile (. == zero) := by
        simp [concat_rule, ha]
      -- apply IH to as
      calc
        List.map normalize ((as ++ [a]).rdropWhile (. == zero)) = List.map normalize (as.rdropWhile (. == zero)) := by rw [eq1]
        _ = as.rdropWhile (. == zero) := by apply ih; exact H_as
      simp_all only [trim, List.mem_append, List.mem_cons, List.not_mem_nil, or_false, true_or, implies_true, forall_const, beq_iff_eq, BEq.rfl, List.rdropWhile_concat_pos, ↓reduceIte]

    · -- case: a is kept, rdropWhile (as ++ [a]) = as ++ [a]
      have concat_rule := List.rdropWhile_concat (. == zero) as a
      have eq2 : (as ++ [a]).rdropWhile (. == zero) = as ++ [a] := by
        simp [concat_rule, ha]
      -- use h (the full hypothesis) to show each element of `as ++ [a]` is fixed by `normalize`
      have H_full : ∀ x ∈ (as ++ [a]), normalize x = x := h
      -- deduce map normalize (as ++ [a]) = as ++ [a] by splitting the append and using map_eq_of_fixed on `as`
      have map_as_eq : (as.map normalize) = as := by
        apply map_eq_of_fixed normalize as
        intro x hx
        -- get membership of x in as ++ [a]
        have : x ∈ as ++ [a] := List.mem_append.2 (Or.inl hx)
        exact H_full x this
      -- deduce normalize a = a from H_full
      have norm_a : normalize a = a := by
        have : a ∈ as ++ [a] := List.mem_append.2 (Or.inr (by simp))
        exact H_full a this
      -- combine
      calc
        List.map normalize ((as ++ [a]).rdropWhile (. == zero)) = List.map normalize (as ++ [a]) := by rw [eq2]
        _ = as.map normalize ++ [normalize a] := by simp [List.map]
        _ = as ++ [a] := by simp [map_as_eq, norm_a]
      simp [trim]
      simp_all only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false, true_or, implies_true, forall_const, beq_iff_eq, ↓reduceIte, not_false_eq_true, List.rdropWhile_concat_neg, or_true]




@[aesop safe]
lemma normalize_idem (x : RawProd) : normalize (normalize x) = normalize x := by
  induction x using RawProd.induction with
  | h_zero => simp only [normalize_zero_eq_zero]
  | h_brak xs ih =>
    simp [normalize]
    let A := xs.map (fun t => normalize t)
    -- show each element of A is fixed by normalize
    have fixedA : ∀ a ∈ A, normalize a = a := by
      intro a ha
      rcases List.mem_map.1 ha with ⟨orig, hmem_orig, heq⟩
      calc
        normalize a = normalize (normalize orig) := by rw [←heq]
        _ = normalize orig := ih orig hmem_orig
        _ = a := by rw [heq]
    -- apply lemma to get map normalize (trim A) = trim A
    have map_on_trim : List.map normalize (trim A) = trim A := map_normalize_trim_of_fixed fixedA
    -- finish by rewriting with map_on_trim and trim_idem
    rw [map_on_trim, trim_idem]

@[aesop safe]
lemma equiv_of_normalize (x : RawProd) : (normalize x).equiv x := by
  simp [equiv, normalize_idem]

@[aesop unsafe 10%]
lemma brak_map_normalize (xs : List RawProd) :
     (brak (List.map normalize xs)).equiv (brak xs) := by
  simp [equiv, normalize]
  congr 1
  simp only [List.map_inj_left, Function.comp_apply, normalize_idem, implies_true]



@[simp]
lemma trim_append_zero (xs : List RawProd) : trim (xs ++ [zero]) = trim xs := by
  induction xs with
  | nil => simp [trim]
  | cons y ys ih =>
    simp only [trim]
    apply List.rdropWhile_concat_pos (. == zero) (y::ys) zero
    rfl


@[aesop safe]
lemma trim_length_leq (xs : List RawProd) : (trim xs).length ≤ xs.length := by
  simp [trim, List.rdropWhile]
  have h : (List.dropWhile (fun x ↦ x == zero) xs.reverse).length ≤ xs.reverse.length := by apply List.length_dropWhile_le (. == zero) xs.reverse
  have h2 : xs.length = xs.reverse.length := by simp only [List.length_reverse]
  rw [h2]
  exact h



@[simp]
lemma trim_brak_eq_brak (xs : List RawProd) : trim [brak xs] = [brak xs] := by
  rfl

@[simp]
lemma trim_append_brak_eq_brak (xs ys : List RawProd) :  trim (xs ++ [brak ys]) = (xs ++ [brak ys]) := by
  simp only [trim, beq_iff_eq, reduceCtorEq, not_false_eq_true, List.rdropWhile_concat_neg]


lemma trim_append_brak_neq_nil (xs ys : List RawProd) : trim (xs ++ [brak ys]) ≠ [] := by
  simp only [trim, beq_iff_eq, reduceCtorEq, not_false_eq_true, List.rdropWhile_concat_neg, ne_eq,
    List.append_eq_nil_iff, List.cons_ne_self, and_false]




lemma trim_eq_nil_iff (xs : List RawProd) : trim xs = [] ↔ ∀ x ∈ xs, x = zero := by
  induction xs using List.reverseRecOn with
  | nil => simp only [trim_nil_eq_nil, List.not_mem_nil, IsEmpty.forall_iff, implies_true]
  | append_singleton ys y ih =>
    constructor
    . intro htrim
      cases y
      . simp_all only [trim_append_zero, List.mem_append, List.mem_cons, List.not_mem_nil, or_false]
        intro z hz
        cases hz with
        | inl hin => exact (htrim z hin)
        | inr hze => exact hze
      . intro z zs
        absurd htrim
        apply trim_append_brak_neq_nil
    . intro heqz
      simp_all only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false, or_true, true_or, implies_true, iff_true, trim_append_zero]




lemma append_trim_eq_imply_neq_zero (xs : List RawProd) (y : RawProd) (h : trim (xs ++ [y]) = xs ++ [y] ) : y ≠ zero := by
  cases y
  case zero =>
    have h2 : (trim xs).length < (xs ++ [zero]).length :=
      -- idk if this is the cleanest but I wanted to try out calc
      calc (trim xs).length ≤ xs.length := trim_length_leq xs
           _      < (xs ++ [zero]).length := by simp only [List.length_append, List.length_cons, List.length_nil, zero_add, lt_add_iff_pos_right, zero_lt_one]
    simp_all only [trim_append_zero, List.length_append, List.length_cons, List.length_nil, zero_add, lt_self_iff_false]

  case brak y => simp only [ne_eq, reduceCtorEq, not_false_eq_true]


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

@[simp] lemma brak_eq_mk (x : RawProd) : ⟦x⟧ = mk x := by rfl

@[simp] lemma zero_eq_zero : mk RawProd.zero = QProd.zero := by rfl

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
