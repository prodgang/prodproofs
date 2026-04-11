import Prod.raw_defs
import Init.Data.List.Basic
import Mathlib.Data.List.DropRight
import Mathlib.Data.Quot

namespace RawProd

/- misc prelim lemmas -/
lemma append_eq_imp_eq_eq {xs ys : List RawProd} {x y : RawProd} (h1 : xs = ys) (h2: x = y) : xs.append [x] = ys.append [y] := by
  subst h2 h1
  simp_all only [List.append_eq]





/- trim -/
def trim (xs : List RawProd) : List RawProd := xs.rdropWhile (. == zero)



lemma trim_nil_eq_nil : trim [] = [] := by simp [trim]

-- @[simp] lemma trim_cons (x : RawProd) (xs : List RawProd) (hnz : x ≠ zero) : trim (x :: xs) = x :: trim xs := by
--   simp [trim]

lemma trim_append_brak_eq_self (xs ys: List RawProd): trim ( xs ++  [brak ys]) = xs ++ [brak ys] := by
  simp only [trim, beq_iff_eq, reduceCtorEq, not_false_eq_true, List.rdropWhile_concat_neg]


-- lemma trim_idem (xs : List RawProd) : trim (trim xs) = trim xs := by
--   apply List.rdropWhile_idempotent


lemma trim_replicate_zero_eq_nil {n : ℕ } : trim (List.replicate n zero) = [] := by
  induction n with
  | zero => simp only [List.replicate_zero, trim_nil_eq_nil]
  | succ n ih => simp only [trim, List.rdropWhile_eq_nil_iff, List.mem_replicate, ne_eq,
    Nat.add_eq_zero_iff, Nat.succ_ne_self, and_false, not_false_eq_true, true_and, beq_iff_eq,
    imp_self, implies_true]



lemma trim_append_zero (xs : List RawProd) : trim (xs ++ [zero]) = trim xs := by
  induction xs with
  | nil => simp [trim]
  | cons y ys ih =>
    simp only [trim]
    apply List.rdropWhile_concat_pos (. == zero) (y::ys) zero
    rfl

-- lemma trim_length_leq (xs : List RawProd) : (trim xs).length ≤ xs.length := by
--   simp [trim, List.rdropWhile]
--   have h : (List.dropWhile (fun x ↦ x == zero) xs.reverse).length ≤ xs.reverse.length := by apply List.length_dropWhile_le (. == zero) xs.reverse
--   have h2 : xs.length = xs.reverse.length := by simp only [List.length_reverse]
--   rw [h2]
--   exact h


lemma trim_append_brak_neq_nil (xs ys : List RawProd) : trim (xs ++ [brak ys]) ≠ [] := by
  simp only [trim, beq_iff_eq, reduceCtorEq, not_false_eq_true, List.rdropWhile_concat_neg, ne_eq,
    List.append_eq_nil_iff, List.cons_ne_self, and_false]


/- normalize -/

/-- Recursively normalize a RawProd by removing trailing zeros at all levels -/
def normalize : RawProd → RawProd
  | zero => zero
  | brak xs => brak (trim (List.map normalize xs))

lemma normalize_zero_eq_zero : normalize zero = zero := by simp only [normalize]

@[simp]
lemma normalize_nil_eq_nil : normalize (brak []) = (brak []) := by simp only [normalize, List.map_nil, trim_nil_eq_nil]

lemma normalize_brak_neq_zero (xs : List RawProd) : normalize (brak xs) ≠ zero := by simp only [normalize, ne_eq, reduceCtorEq, not_false_eq_true]


lemma zero_eq_normalize_eq_zero {x : RawProd} (heqz : zero = x.normalize ) : x = zero := by
  cases x <;> simp_all only [normalize, normalize_zero_eq_zero, reduceCtorEq]

lemma normalize_eq_zero_eq_zero {x : RawProd} (heqz : x.normalize = zero ) : x = zero := by
  cases x <;> simp_all only [normalize, normalize_zero_eq_zero, reduceCtorEq]


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





/- equiv -/

def equiv (x y : RawProd) : Prop :=
  normalize x = normalize y


theorem equiv_refl : ∀ x, equiv x x := by
  intro x; cases x <;> simp only [equiv]

theorem equiv_symm {x y : RawProd }: equiv x y → equiv y x := by
  intro h
  cases x <;> cases y <;> simp_all [equiv, normalize]


theorem equiv_trans {x y z : RawProd }: equiv x y → equiv y z → equiv x z := by
  intro h1 h2
  cases x <;> cases y <;> cases z <;> simp_all only [equiv]

  /-- Setoid instance for productive numbers -/
instance : Setoid RawProd where
  r := equiv
  iseqv := ⟨@equiv_refl, @equiv_symm, @equiv_trans⟩



--  lemma not_brak_equiv_zero (xs : List RawProd) : ¬ (brak xs).equiv zero := by
--   simp only [equiv, normalize_zero_eq_zero, normalize_brak_neq_zero, not_false_eq_true]

--  lemma not_zero_equiv_brak (xs : List RawProd) : ¬ zero.equiv (brak xs) := by
--   simp only [equiv, normalize_zero_eq_zero, normalize, reduceCtorEq, not_false_eq_true]


@[simp]
lemma equiv_zero_eq_zero {x : RawProd} : equiv zero x →  x = zero := by
  intro hequiv
  simp only [equiv] at hequiv
  cases x
  case zero => rfl
  case brak xs => simp_all only [normalize, reduceCtorEq]


@[simp]
lemma zero_equiv_eq_zero {x : RawProd} : equiv x zero →  x = zero := by
  intro hequiv
  simp only [equiv] at hequiv
  cases x
  case zero => rfl
  case brak xs => simp_all only [normalize, reduceCtorEq]


lemma equiv_normalize_eq {x y : RawProd }: equiv x y → normalize x = normalize y := by
  simp only [equiv, imp_self]


lemma equiv_of_normalize {x : RawProd} : (normalize x).equiv x := by
  simp only [equiv, normalize_idem]

lemma brak_map_normalize (xs : List RawProd) :
     (brak (List.map normalize xs)).equiv (brak xs) := by
  simp [equiv, normalize]
  congr 1
  simp only [List.map_inj_left, Function.comp_apply, normalize_idem, implies_true]




/- allzero -/

def allzero (xs : List RawProd ): Prop := xs = List.replicate xs.length zero

instance decidable_allzero (xs : List RawProd) [DecidableEq RawProd] :
  Decidable (allzero xs) := by
  dsimp [allzero]
  infer_instance


-- lemma allzero_nil : allzero [] := by simp only [allzero, List.length_nil, List.replicate_zero]

/-alternative definition-/
lemma allzero_iff {xs : List RawProd} : allzero xs ↔ ∀ x ∈ xs, x = zero := by
  simp only [allzero]
  constructor
  . intro haz
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


lemma allzero_cons {x : RawProd} {xs : List RawProd} (haz : allzero (x::xs)) : x = zero ∧ allzero xs := by
  simp_all only [allzero, List.length_cons]
  rw [List.replicate_succ, List.cons.injEq] at haz
  exact haz


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
      simp_all only [allzero, List.length_append, List.length_cons, List.length_nil, Nat.zero_add]
      simp only [List.replicate_succ', List.append_singleton_inj, trim_append_zero] at heqz ⊢
      have h :=  ih.mpr heqz.1
      rw [heqz.1] at h
      exact h

@[simp]
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



-- If two lists have the same trim, prepending the same element gives the same trim.
lemma trim_cons_congr (a : RawProd) {as bs : List RawProd}
    (h : trim as = trim bs) : trim (a :: as) = trim (a :: bs) := by
  simp only [trim_cons]
  have haz : allzero (a :: as) ↔ allzero (a :: bs) := by
    constructor <;> intro haz <;> obtain ⟨ha, hazs⟩ := allzero_cons haz
    · exact allzero_iff.mpr fun x hx => (List.mem_cons.mp hx).elim
        (·.trans ha) (allzero_iff.mp (trim_eq_nil_iff.mp (h ▸ trim_eq_nil_iff.mpr hazs)) x)
    · exact allzero_iff.mpr fun x hx => (List.mem_cons.mp hx).elim
        (·.trans ha) (allzero_iff.mp (trim_eq_nil_iff.mp (h.symm ▸ trim_eq_nil_iff.mpr hazs)) x)
  simp only [haz, h]

theorem cons_equiv_cons_iff {x y : RawProd} {xs ys : List RawProd} : (x.equiv y ∧ (brak xs).equiv (brak ys)) ↔ (brak (x :: xs)).equiv (brak (y :: ys)) := by
constructor
. intro ⟨hxy, hbb⟩
  simp_all only [equiv, normalize, brak.injEq, List.map_cons]
  exact trim_cons_congr _ hbb
. intro h
  simp_all only [equiv, normalize, List.map_cons, trim_cons, brak.injEq]
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

lemma brak_equiv_nil_iff_allzero {xs : List RawProd} : (brak xs).equiv (brak []) ↔ allzero xs := by
  simp only [equiv, normalize, List.map_nil, trim_nil_eq_nil, brak.injEq]
  rw [trim_eq_nil_iff]
  simp only [allzero_iff, List.mem_map, forall_exists_index, and_imp]
  constructor
  · intro h x hx
    exact normalize_eq_zero_eq_zero (h (normalize x) x hx rfl)
  · intro h x y hy hyx
    subst hyx
    rw [h y hy, normalize_zero_eq_zero]


lemma nil_equiv_brak_iff_allzero {xs : List RawProd} : (brak []).equiv (brak xs) ↔ allzero xs := by
  constructor
  · intro h; exact brak_equiv_nil_iff_allzero.mp (equiv_symm h)
  · intro h; exact equiv_symm (brak_equiv_nil_iff_allzero.mpr h)

end RawProd



/-- Productive numbers as a quotient type -/
def QProd := Quotient RawProd.instSetoid

namespace QProd

/-- Constructor from raw productive number -/
def mk : RawProd → QProd := Quotient.mk RawProd.instSetoid

/-- Zero element -/
def zero : QProd := mk RawProd.zero

/-- Get the normalized representative -/
def rep : QProd → RawProd :=
  Quotient.lift RawProd.normalize @RawProd.equiv_normalize_eq

def ofList (xs : List QProd) : QProd :=
  mk (RawProd.brak (xs.map rep))

lemma brak_eq_mk (x : RawProd) : ⟦x⟧ = mk x := by rfl

lemma mk_zero_eq_zero : mk RawProd.zero = QProd.zero := by rfl

lemma mk_nil_eq_nil : mk (RawProd.brak []) = ofList [] := by rfl

lemma ofList_map_mk_eq_mk_brak (xs : List RawProd) :
    ofList (List.map mk xs) = mk (RawProd.brak xs) := by
  simp only [ofList, rep, List.map_map]
  apply Quotient.sound
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


@[simp]
lemma mk_rep_eq {q : QProd} : mk (rep q) = q := by
  -- reduce to the mk-a case
  revert q
  apply Quotient.ind
  intro a
  show mk (RawProd.normalize a) = mk a
  apply Quotient.sound
  exact RawProd.equiv_of_normalize

@[simp]
lemma rep_equiv_eq {x y : QProd } :  x.rep.equiv y.rep → x = y := by
  intro hequiv
  calc
    x = mk (rep x) := (mk_rep_eq).symm
    _ = mk (rep y) := Quotient.sound hequiv
    _ = y := mk_rep_eq

/-! ### Lifting API

  Every QProd operation `F` is defined via `Quotient.liftOn₂`, so `F (mk a) (mk b) = mk (f_raw a b)`
  holds definitionally (proved by `rfl`). The `lift_raw_eq₁/₂/₃` lemmas encapsulate the full
  `Quotient.ind + Eq.trans + congr_arg mk` pattern, making every QProd lifting theorem a one-liner. -/

/-- Lift a unary QProd equation from a raw equation. -/
lemma lift_eq₁ {F G : QProd → QProd} {f g : RawProd → RawProd}
    (h : ∀ a, f a = g a)
    (hF : ∀ a, F (mk a) = mk (f a) := by intro _; rfl)
    (hG : ∀ a, G (mk a) = mk (g a) := by intro _; rfl) :
    ∀ x, F x = G x :=
  Quotient.ind (fun a => (hF a).trans ((congr_arg mk (h a)).trans (hG a).symm))

/-- Lift a binary QProd equation from a raw equation. -/
lemma lift_eq₂ {F G : QProd → QProd → QProd} {f g : RawProd → RawProd → RawProd}
    (h : ∀ a b, f a b = g a b)
    (hF : ∀ a b, F (mk a) (mk b) = mk (f a b) := by intro _ _; rfl)
    (hG : ∀ a b, G (mk a) (mk b) = mk (g a b) := by intro _ _; rfl) :
    ∀ x y, F x y = G x y :=
  fun x y => Quotient.ind₂ (fun a b =>
    (hF a b).trans ((congr_arg mk (h a b)).trans (hG a b).symm)) x y

/-- Lift a ternary QProd equation from a raw equation. -/
lemma lift_eq₃ {F G : QProd → QProd → QProd → QProd}
    {f g : RawProd → RawProd → RawProd → RawProd}
    (h : ∀ a b c, f a b c = g a b c)
    (hF : ∀ a b c, F (mk a) (mk b) (mk c) = mk (f a b c) := by intro _ _ _; rfl)
    (hG : ∀ a b c, G (mk a) (mk b) (mk c) = mk (g a b c) := by intro _ _ _; rfl) :
    ∀ x y z, F x y z = G x y z :=
  fun x y z => Quotient.inductionOn₃ x y z (fun a b c =>
    (hF a b c).trans ((congr_arg mk (h a b c)).trans (hG a b c).symm))

end QProd
