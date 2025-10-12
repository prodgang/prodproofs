import Prod.raw_defs

namespace RawProd

/-- Remove trailing zeros from a list -/
def trim : List RawProd → List RawProd
  | [] => []
  | x :: xs =>
    match trim xs with
    | [] => if x == zero then [] else [x]
    | ys => x :: ys


/-- Recursively normalize a RawProd by removing trailing zeros at all levels -/
def normalize : RawProd → RawProd
  | zero => zero
  | cons xs => cons (trim (List.map normalize xs))

-- The equiv definition stays the same:
def equiv (x y : RawProd) : Prop :=
  match x, y with
  | zero, zero => True
  | zero, cons _ => False
  | cons _, zero => False
  | cons xs, cons ys => trim (List.map normalize xs) = trim (List.map normalize ys)


theorem equiv_refl : ∀ x, equiv x x := by
  intro x
  cases x
  · simp [equiv]
  · simp [equiv]

theorem equiv_symm : ∀ x y, equiv x y → equiv y x := by
  intro x y h
  cases x <;> cases y <;> simp only [equiv] at h ⊢
  · exact h.symm

theorem equiv_trans : ∀ x y z, equiv x y → equiv y z → equiv x z := by
  intro x y z h1 h2
  cases x <;> cases y <;> cases z <;> simp_all only [equiv]

  /-- Setoid instance for productive numbers -/
instance : Setoid RawProd where
  r := equiv
  iseqv := ⟨equiv_refl, @equiv_symm, @equiv_trans⟩


-- Now normalize_eq_of_equiv becomes provable:
lemma normalize_eq_of_equiv : ∀ x y, equiv x y → normalize x = normalize y := by
  intro x y h
  cases x <;> cases y <;> simp [equiv] at h
  · rfl
  · rename_i xs ys
    simp only [normalize]
    congr 1


lemma trim_idem (xs : List RawProd) : trim (trim xs) = trim xs := by
  induction xs using List.recOn with
  | nil => simp [trim]
  | cons x xs ih =>
    simp [trim]
    split <;> rename_i h
    · split_ifs with hx
      · simp only [trim]
      · simp [trim, hx]
    . simp only [trim, beq_iff_eq]
      simp_all only [imp_false]



-- lemma map_normalize_idem (xs : List RawProd) :
--     List.map normalize (List.map normalize xs) = List.map normalize xs := by
--   ext i
--   simp only [List.get_map]
--   exact normalize_idem (xs.get i)

-- lemma trim_map_normalize_idem (xs : List RawProd) :
--     trim (List.map normalize (trim (List.map normalize xs))) = trim (List.map normalize xs) := by
--   rw [← map_normalize_idem (trim (List.map normalize xs))]
--   rw [trim_idem]

@[aesop safe]
lemma normalize_idem (x : RawProd) : normalize (normalize x) = normalize x := by
  induction x using RawProd.induction with
  | h_zero => simp [normalize]
  | h_cons xs ih =>
    simp only [normalize]
    congr 2
    sorry
    -- cant close, skipping for now
--     xs : List RawProd
-- ih : ∀ x ∈ xs, x.normalize.normalize = x.normalize
-- ⊢ List.map normalize (trim (List.map normalize xs)) = List.map normalize xs


@[aesop unsafe 10%]
lemma cons_map_normalize (xs : List RawProd) :
    equiv (cons (List.map normalize xs)) (cons xs) := by
  simp [equiv]
  congr 1
  --simp only [List.map_inj_left, Function.comp_apply, normalize_idem, implies_true]
  simp only [List.map_inj_left, Function.comp_apply]
  simp [normalize_idem]


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
  Quotient.lift RawProd.normalize RawProd.normalize_eq_of_equiv

def ofList (xs : List QProd) : QProd :=
  mk (RawProd.cons (xs.map normalize))

@[simp] lemma brak_eq_mk (x : RawProd) : ⟦x⟧ = mk x := by rfl

@[simp] lemma zero_eq_zero : mk RawProd.zero = QProd.zero := by rfl

lemma ofList_map_mk_eq_mk_cons (xs : List RawProd) :
    ofList (List.map mk xs) = mk (RawProd.cons xs) := by
  simp only [ofList, normalize, List.map_map]
  apply Quotient.sound
  have hl : Quotient.lift RawProd.normalize RawProd.normalize_eq_of_equiv ∘ mk = RawProd.normalize :=
    Quotient.lift_comp_mk _ _
  rw [hl]
  exact RawProd.cons_map_normalize xs

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
    rw [ofList_map_mk_eq_mk_cons] at h_cons
    exact h_cons

end QProd
