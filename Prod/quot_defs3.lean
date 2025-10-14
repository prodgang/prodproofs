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

@[simp]
lemma normalize_zero_eq_zero : normalize zero = zero := by simp only [normalize]

-- The equiv definition stays the same:
def equiv_old (x y : RawProd) : Prop :=
  match x, y with
  | zero, zero => True
  | zero, cons _ => False
  | cons _, zero => False
  | cons xs, cons ys => trim (List.map normalize xs) = trim (List.map normalize ys)

def equiv (x y : RawProd) : Prop :=
  normalize x = normalize y


theorem equiv_refl : ∀ x, equiv x x := by
  intro x
  cases x <;> simp [equiv]

-- theorem equiv_symm_old : ∀ x y, equiv x y → equiv y x := by
--   intro x y h
--   cases x <;> cases y <;> simp only [equiv] at h ⊢
--   · exact h.symm

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

theorem map_normalize_trim_of_fixed {l : List RawProd}
  (h : ∀ a ∈ l, normalize a = a) :
  List.map normalize (trim l) = trim l := by
  induction l with
  | nil => simp [trim]
  | cons x xs ih =>
    -- compute trim (x :: xs) according to definition
    simp [trim]
    let t := trim xs
    cases t with
    | nil =>
      -- trim xs = []
      -- trim (x::xs) = if x == zero then [] else [x]
      by_cases hx : x == RawProd.zero
      · -- case x == zero: both sides are []
        simp_all only [List.mem_cons, or_true, implies_true, forall_const, forall_eq_or_imp, beq_iff_eq, ↓reduceIte,
          and_true]
        subst hx
        split
        next x heq => simp_all only [List.map_nil]
        next x x_1 =>
          simp_all only [imp_false, List.map_cons, normalize_zero_eq_zero]
      . simp_all only [List.mem_cons, or_true, implies_true, forall_const, forall_eq_or_imp, beq_iff_eq, ↓reduceIte]
        obtain ⟨left, right⟩ := h
        split
        next x_1 heq => simp_all only [List.map_nil, List.map_cons]
        next x_1 x_2 => simp_all only [imp_false, List.map_cons]
    | cons y ys =>
      -- trim xs = y :: ys so trim (x::xs) = x :: (y :: ys)
      -- need to show map normalize (x :: y :: ys) = x :: y :: ys
      -- split into two facts: normalize x = x and map normalize (trim xs) = trim xs
      simp_all only [List.mem_cons, or_true, implies_true, forall_const, forall_eq_or_imp]
      obtain ⟨left, right⟩ := h
      split
      next x_1 heq =>
        simp_all only [List.map_nil]
        split
        next h =>
          subst h
          simp_all only [List.map_nil]
        next h => simp_all only [List.map_cons, List.map_nil]
      next x_1 x_2 => simp_all only [imp_false, List.map_cons]

@[aesop safe]
theorem normalize_idem (x : RawProd) : normalize (normalize x) = normalize x := by
  induction x using RawProd.induction with
  | h_zero => simp only [normalize_zero_eq_zero]
  | h_cons xs ih =>
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
lemma cons_map_normalize (xs : List RawProd) :
     (cons (List.map normalize xs)).equiv (cons xs) := by
  simp [equiv, normalize]
  congr 1
  simp only [List.map_inj_left, Function.comp_apply, normalize_idem, implies_true]



@[simp]
lemma trim_append_zero (xs : List RawProd) : trim (xs ++ [zero]) = trim xs := by
  induction xs with
  | nil => simp [trim]
  | cons y ys ih => simp_all only [List.cons_append, trim, beq_iff_eq]

@[simp]
lemma trim_length_leq (xs : List RawProd) : (trim xs).length ≤ xs.length := by
  induction xs using  List.reverseRecOn with
  | nil => simp only [trim, List.length_nil, le_refl]
  | append_singleton ys y ih =>
    cases y
    case zero => simp [trim_append_zero]; linarith
    case cons yy =>
      --let ys' := ys ++ [cons yy]
      --rw [← (by rfl : ys' = ys ++ [cons yy])]
      rw [trim.eq_def]
      --simp_all only [beq_iff_eq, List.length_append, List.length_cons, List.length_nil, zero_add]
      simp_all
      split
      next x heq => simp_all only [List.append_eq_nil_iff, List.cons_ne_self, and_false]
      next x x_1 xs heq =>
        split
        next x_2 heq_1 =>
          split
          next h =>
            subst h
            simp_all only [List.length_nil, le_add_iff_nonneg_left, zero_le]
          next h => simp_all only [List.length_cons, List.length_nil, zero_add, le_add_iff_nonneg_left, zero_le]
        next x_2 x_3 =>
          simp_all only [imp_false, List.length_cons, add_le_add_iff_right]
          linarith





theorem trim_length_leq_gpt (xs : List RawProd) : (trim xs).length ≤ xs.length := by
  induction xs with
  | nil =>
    -- trim [] = []
    simp [trim]
  | cons x xs ih =>
    -- trim (x :: xs) = match trim xs with ... ; let t := trim xs and do case split
    let t := trim xs
    cases t with
    | nil =>
      -- trim xs = []
      -- so trim (x :: xs) = if x == zero then [] else [x]
      simp [trim]
      -- do a case split on whether x == zero
      by_cases hx : x = RawProd.zero
      · -- case: x == zero, so trim (x::xs) = []
        -- rewrite the `if` using the hypothesis and finish
        rw [if_pos hx]
        subst hx
        simp_all only [trim_length_leq]
        split
        next x heq => simp_all only [List.length_nil, le_add_iff_nonneg_left, zero_le]
        next x x_1 => simp_all only [imp_false, List.length_cons, add_le_add_iff_right, trim_length_leq]
      · -- case: x != zero, so trim (x::xs) = [x]
        rw [if_neg hx]
        -- 1 ≤ 1 + xs.length, which is succ_le_succ (0 ≤ xs.length)
        simp_all only [trim_length_leq]
        split
        next x_1 heq => simp_all only [List.length_cons, List.length_nil, zero_add, le_add_iff_nonneg_left, zero_le]
        next x_1 x_2 => simp_all only [imp_false, List.length_cons, add_le_add_iff_right, trim_length_leq]
    | cons y ys =>
      -- trim xs = y :: ys, so trim (x :: xs) = x :: ys
      -- lengths: (x :: ys).length = 1 + ys.length and (trim xs).length = 1 + ys.length
      -- use IH: (trim xs).length ≤ xs.length, i.e. 1 + ys.length ≤ xs.length.
      -- then 1 + ys.length ≤ 1 + xs.length by Nat.le_succ.
      have hlen : (trim xs).length = Nat.succ ys.length := by
        -- by definition of t
        simp [t]
      calc
        (trim (x :: xs)).length = (x :: ys).length := by simp [trim, t]


        _ = Nat.succ ys.length := by simp
        _ = (trim xs).length := by rw [hlen]
        _ ≤ xs.length := by exact ih
        _ ≤ Nat.succ xs.length := by apply Nat.le_succ


theorem trim_length_leq_again (xs : List RawProd) : (trim xs).length ≤ xs.length := by
  induction xs with
  | nil =>
    -- trim [] = []
    simp [trim]
  | cons x xs ih =>
    let t := trim xs
    cases t with
    | nil =>
      -- trim xs = []
      -- so trim (x :: xs) = if x == zero then [] else [x]
      simp [trim]
      by_cases hx : x == RawProd.zero
      · -- trim (x::xs) = []
        simp_all only [trim_length_leq, beq_iff_eq, ↓reduceIte]
        subst hx
        split
        next x heq => simp_all only [List.length_nil, le_add_iff_nonneg_left, zero_le]
        next x x_1 => simp_all only [imp_false, List.length_cons, add_le_add_iff_right, trim_length_leq]
      · -- trim (x::xs) = [x]
        simp_all only [trim_length_leq, beq_iff_eq, ↓reduceIte]
        split
        next x_1 heq => simp_all only [List.length_cons, List.length_nil, zero_add, le_add_iff_nonneg_left, zero_le]
        next x_1 x_2 => simp_all only [imp_false, List.length_cons, add_le_add_iff_right, trim_length_leq]
    | cons y ys =>
      -- Here t := trim xs and the `cases` gives the definitional equality `trim xs = y :: ys`.
      -- Use it to reduce `trim (x :: xs)` to `x :: ys`.
      have tr_eq : trim xs = y :: ys := by
        simp_all only [trim_length_leq]
        sorry
      -- compute `trim (x::xs)` using that equality and finish by length algebra
      have hdef : trim (x :: xs) = x :: ys := by
        -- unfold the definition and rewrite the inner `trim xs` to `y :: ys`
        dsimp [trim]
        rw [tr_eq]
        -- now the `match` reduces to the expected branch
        simp only [List.cons.injEq, List.cons_ne_self, and_false]

      -- finish by comparing lengths
      calc
        (trim (x :: xs)).length = (x :: ys).length := by rw [hdef]
        _ = Nat.succ ys.length := by simp
        _ = (trim xs).length := by rw [tr_eq]; simp
        _ ≤ xs.length := ih

      simp_all only [List.length_cons, le_add_iff_nonneg_right, zero_le]





lemma append_trim_eq_imply_neq_zero (xs : List RawProd) (y : RawProd) (h : trim (xs ++ [y]) = xs ++ [y] ) : y ≠ zero := by
  cases y
  case zero =>
    --simp aaaaaaaaaaaa
    sorry
  case cons y => sorry


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
  mk (RawProd.cons (xs.map normalize))

@[simp] lemma brak_eq_mk (x : RawProd) : ⟦x⟧ = mk x := by rfl

@[simp] lemma zero_eq_zero : mk RawProd.zero = QProd.zero := by rfl

lemma ofList_map_mk_eq_mk_cons (xs : List RawProd) :
    ofList (List.map mk xs) = mk (RawProd.cons xs) := by
  simp only [ofList, normalize, List.map_map]
  apply Quotient.sound
  have hl : Quotient.lift RawProd.normalize RawProd.equiv_normalize_eq ∘ mk = RawProd.normalize :=
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
