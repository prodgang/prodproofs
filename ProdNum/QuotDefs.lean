/-
Copyright (c) 2024 Edwin Agnew. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Edwin Agnew
-/
import ProdNum.PreProdDefs
import Init.Data.List.Basic
import Mathlib.Data.List.DropRight
import Mathlib.Data.Quot

/-!
# Productive Numbers — Normalization and Quotient

Defines the normalization pipeline for `PreProdNum` and the quotient type `ProdNum`.

## Main definitions

- `PreProdNum.trim`: removes trailing `zero`s from a list
- `PreProdNum.normalize`: recursively trims a `PreProdNum`
- `PreProdNum.equiv`: setoid on `PreProdNum`, defined as `normalize x = normalize y`
- `ProdNum`: the quotient `PreProdNum / equiv`
- `ProdNum.mk`, `ProdNum.rep`, `ProdNum.ofList`, `ProdNum.induction`: basic API
- `ProdNum.lift_eq₁`, `lift_eq₂`, `lift_eq₃`: lifting API for ProdNum equalities
-/

namespace PreProdNum

private lemma append_eq_imp_eq_eq {xs ys : List PreProdNum} {x y : PreProdNum}
    (h1 : xs = ys) (h2 : x = y) : xs.append [x] = ys.append [y] := by
  subst h2 h1; simp_all only [List.append_eq]


/-! ### Trim -/
def trim (xs : List PreProdNum) : List PreProdNum := xs.rdropWhile (. == zero)



lemma trim_nil : trim [] = [] := by simp only [trim, List.rdropWhile_nil]

lemma trim_append_brak_eq_self (xs ys: List PreProdNum): trim ( xs ++  [brak ys]) = xs ++ [brak ys] := by
  simp only [trim, beq_iff_eq, reduceCtorEq, not_false_eq_true, List.rdropWhile_concat_neg]


lemma trim_replicate_zero_eq_nil {n : ℕ } : trim (List.replicate n zero) = [] := by
  induction n with
  | zero => simp only [List.replicate_zero, trim_nil]
  | succ n ih => simp only [trim, List.rdropWhile_eq_nil_iff, List.mem_replicate, ne_eq,
    Nat.add_eq_zero_iff, Nat.succ_ne_self, and_false, not_false_eq_true, true_and, beq_iff_eq,
    imp_self, implies_true]



lemma trim_append_zero (xs : List PreProdNum) : trim (xs ++ [zero]) = trim xs := by
  induction xs with
  | nil => simp only [trim]; apply List.rdropWhile_concat_pos; rfl
  | cons y ys ih =>
    simp only [trim]
    apply List.rdropWhile_concat_pos (. == zero) (y::ys) zero
    rfl

lemma trim_append_brak_neq_nil (xs ys : List PreProdNum) : trim (xs ++ [brak ys]) ≠ [] := by
  simp only [trim, beq_iff_eq, reduceCtorEq, not_false_eq_true, List.rdropWhile_concat_neg, ne_eq,
    List.append_eq_nil_iff, List.cons_ne_self, and_false]


/-! ### Normalize -/

/-- Recursively normalize a PreProdNum by removing trailing zeros at all levels -/
def normalize : PreProdNum → PreProdNum
  | zero => zero
  | brak xs => brak (trim (List.map normalize xs))

lemma normalize_zero : normalize zero = zero := by simp only [normalize]

@[simp]
lemma normalize_nil : normalize nil = nil := by simp only [normalize, List.map_nil, trim_nil]

lemma zero_eq_normalize_eq_zero {x : PreProdNum} (heqz : zero = x.normalize ) : x = zero := by
  cases x <;> simp_all only [normalize, normalize_zero, reduceCtorEq]

lemma normalize_eq_zero_eq_zero {x : PreProdNum} (heqz : x.normalize = zero ) : x = zero := by
  cases x <;> simp_all only [normalize, normalize_zero, reduceCtorEq]


lemma normalize_idem (x : PreProdNum) : normalize (normalize x) = normalize x := by
  induction x using PreProdNum.induction with
  | h_zero => simp only [normalize_zero]
  | h_brak xs ih =>
    induction xs using List.reverseRecOn with
    | nil => simp only [normalize, List.map_nil, trim_nil]
    | append_singleton xx x ihxx =>
      simp_all [normalize]
      cases x
      case zero => simp_all only [trim, normalize_zero, BEq.rfl, List.rdropWhile_concat_pos];
      case brak xx' =>
        simp_all only [normalize, trim_append_brak_eq_self, List.map_append, List.map_map, List.map_cons, List.map_nil]
        rw [← List.append_eq, ← List.append_eq]
        apply append_eq_imp_eq_eq
        · simp only [List.map_inj_left, Function.comp_apply]; intro a ha; apply ih; left; exact ha
        · have hxx : (brak xx').normalize.normalize = (brak xx').normalize := by apply ih; right; rfl
          simp only [normalize] at hxx
          exact hxx





/-! ### Equivalence relation -/

def equiv (x y : PreProdNum) : Prop :=
  normalize x = normalize y


theorem equiv_refl : ∀ x, equiv x x := by
  intro x; cases x <;> simp only [equiv]

theorem equiv_symm {x y : PreProdNum }: equiv x y → equiv y x := by
  intro h
  cases x <;> cases y <;> simp_all [equiv, normalize]


theorem equiv_trans {x y z : PreProdNum }: equiv x y → equiv y z → equiv x z := by
  intro h1 h2
  cases x <;> cases y <;> cases z <;> simp_all only [equiv]

/-- Setoid instance for productive numbers -/
instance : Setoid PreProdNum where
  r := equiv
  iseqv := ⟨@equiv_refl, @equiv_symm, @equiv_trans⟩


@[simp]
lemma equiv_zero_eq_zero {x : PreProdNum} : equiv zero x →  x = zero := by
  intro hequiv
  simp only [equiv] at hequiv
  cases x
  case zero => rfl
  case brak xs => simp_all only [normalize, reduceCtorEq]


@[simp]
lemma zero_equiv_eq_zero {x : PreProdNum} : equiv x zero →  x = zero := by
  intro hequiv
  simp only [equiv] at hequiv
  cases x
  case zero => rfl
  case brak xs => simp_all only [normalize, reduceCtorEq]


lemma equiv_normalize_eq {x y : PreProdNum }: equiv x y → normalize x = normalize y := by
  simp only [equiv, imp_self]


lemma equiv_of_normalize {x : PreProdNum} : (normalize x).equiv x := by
  simp only [equiv, normalize_idem]

lemma brak_map_normalize (xs : List PreProdNum) :
     (brak (List.map normalize xs)).equiv (brak xs) := by
  simp only [equiv, normalize, List.map_map, brak.injEq]
  congr 1
  simp only [List.map_inj_left, Function.comp_apply, normalize_idem, implies_true]




/-! ### All-zero lists -/

def allzero (xs : List PreProdNum ): Prop := xs = List.replicate xs.length zero

instance decidable_allzero (xs : List PreProdNum) [DecidableEq PreProdNum] :
  Decidable (allzero xs) := by
  dsimp only [allzero]
  infer_instance


lemma allzero_iff {xs : List PreProdNum} : allzero xs ↔ ∀ x ∈ xs, x = zero := by
  simp only [allzero]
  constructor
  . intro haz
    apply (List.eq_replicate_iff.mp haz).2
  . intro h
    apply List.eq_replicate_iff.mpr
    constructor
    . rfl
    . exact h



lemma not_allzero_append_zero {xs : List PreProdNum} (hnaz: ¬ PreProdNum.allzero (xs ++ [zero])) : ¬ PreProdNum.allzero xs := by
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


lemma allzero_cons {x : PreProdNum} {xs : List PreProdNum} (haz : allzero (x::xs)) : x = zero ∧ allzero xs := by
  simp_all only [allzero, List.length_cons]
  rw [List.replicate_succ, List.cons.injEq] at haz
  exact haz

lemma allzero_get_zero {xs : List PreProdNum} (h : allzero xs) (i : ℕ) : get xs i = zero := by
  rw [allzero_iff] at h
  induction xs generalizing i with
  | nil => simp only [get_nil]
  | cons xh xt ih =>
    cases i with
    | zero => rw [get_cons_zero]; exact h xh (by simp only [List.mem_cons, true_or])
    | succ n => rw [get_cons_succ]; exact ih (fun x hm => h x (List.mem_cons_of_mem _ hm)) n



lemma trim_eq_nil_iff {xs : List PreProdNum} : trim xs = [] ↔ PreProdNum.allzero xs := by
  induction xs using List.reverseRecOn with
  | nil => simp only [allzero, trim_nil, List.length_nil, List.replicate_zero]
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
lemma trim_allzero_eq_nil {xs : List PreProdNum } (hz : allzero xs) : trim xs = [] := by
  simp only [allzero] at hz
  rw [hz]
  apply trim_replicate_zero_eq_nil



lemma trim_cons {x : PreProdNum} {xs : List PreProdNum} : trim (x::xs) = if (allzero (x::xs)) then [] else x :: trim xs := by
  split_ifs
  case pos hpos => exact trim_eq_nil_iff.mpr hpos
  case neg hneg =>
    induction xs using List.reverseRecOn with
    | nil =>
      rw [trim_nil]
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



lemma trim_cons_congr (a : PreProdNum) {as bs : List PreProdNum}
    (h : trim as = trim bs) : trim (a :: as) = trim (a :: bs) := by
  simp only [trim_cons]
  have haz : allzero (a :: as) ↔ allzero (a :: bs) := by
    constructor <;> intro haz <;> obtain ⟨ha, hazs⟩ := allzero_cons haz
    · exact allzero_iff.mpr fun x hx => (List.mem_cons.mp hx).elim
        (·.trans ha) (allzero_iff.mp (trim_eq_nil_iff.mp (h ▸ trim_eq_nil_iff.mpr hazs)) x)
    · exact allzero_iff.mpr fun x hx => (List.mem_cons.mp hx).elim
        (·.trans ha) (allzero_iff.mp (trim_eq_nil_iff.mp (h.symm ▸ trim_eq_nil_iff.mpr hazs)) x)
  simp only [haz, h]

theorem cons_equiv_cons_iff {x y : PreProdNum} {xs ys : List PreProdNum} : (x.equiv y ∧ (brak xs).equiv (brak ys)) ↔ (brak (x :: xs)).equiv (brak (y :: ys)) := by
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

lemma brak_equiv_nil_iff_allzero {xs : List PreProdNum} : (brak xs).equiv nil ↔ allzero xs := by
  simp only [equiv, normalize, List.map_nil, trim_nil, brak.injEq]
  rw [trim_eq_nil_iff]
  simp only [allzero_iff, List.mem_map, forall_exists_index, and_imp]
  constructor
  · intro h x hx
    exact normalize_eq_zero_eq_zero (h (normalize x) x hx rfl)
  · intro h x y hy hyx
    subst hyx
    rw [h y hy, normalize_zero]


lemma nil_equiv_brak_iff_allzero {xs : List PreProdNum} : nil.equiv (brak xs) ↔ allzero xs := by
  constructor
  · intro h; exact brak_equiv_nil_iff_allzero.mp (equiv_symm h)
  · intro h; exact equiv_symm (brak_equiv_nil_iff_allzero.mpr h)

end PreProdNum



/-- Productive numbers as a quotient type -/
def ProdNum := Quotient PreProdNum.instSetoid

namespace ProdNum

/-- Constructor from a `PreProdNum` -/
def mk : PreProdNum → ProdNum := Quotient.mk PreProdNum.instSetoid

/-- Zero element -/
def zero : ProdNum := mk PreProdNum.zero

/-- Get the normalized representative -/
def rep : ProdNum → PreProdNum :=
  Quotient.lift PreProdNum.normalize @PreProdNum.equiv_normalize_eq

def ofList (xs : List ProdNum) : ProdNum :=
  mk (PreProdNum.brak (xs.map rep))

abbrev nil : ProdNum := mk PreProdNum.nil

lemma brak_eq_mk (x : PreProdNum) : ⟦x⟧ = mk x := by rfl

lemma mk_zero_eq_zero : mk PreProdNum.zero = ProdNum.zero := by rfl

lemma mk_nil_eq_nil : mk (PreProdNum.nil) = ofList [] := by rfl

lemma ofList_map_mk_eq_mk_brak (xs : List PreProdNum) :
    ofList (List.map mk xs) = mk (PreProdNum.brak xs) := by
  simp only [ofList, rep, List.map_map]
  apply Quotient.sound
  exact PreProdNum.brak_map_normalize xs


/-- Induction principle for ProdNum -/
theorem induction {P : ProdNum → Prop}
    (h_zero : P zero)
    (h_cons : ∀ xs : List ProdNum, (∀ x ∈ xs, P x) → P (ofList xs)) :
    ∀ x, P x := by
  intro x
  apply Quotient.ind
  apply PreProdNum.induction
  · exact h_zero
  · intro pre_xs ih_pre
    simp only [brak_eq_mk] at ih_pre ⊢
    let xs: List ProdNum := List.map mk pre_xs
    specialize h_cons xs
    simp only [List.mem_map, forall_exists_index, and_imp,
               forall_apply_eq_imp_iff₂, xs] at h_cons
    specialize h_cons ih_pre
    rw [ofList_map_mk_eq_mk_brak] at h_cons
    exact h_cons


@[simp]
lemma mk_rep_eq {q : ProdNum} : mk (rep q) = q := by
  revert q
  apply Quotient.ind
  intro a
  show mk (PreProdNum.normalize a) = mk a
  apply Quotient.sound
  exact PreProdNum.equiv_of_normalize

@[simp]
lemma rep_equiv_eq {x y : ProdNum } :  x.rep.equiv y.rep → x = y := by
  intro hequiv
  calc
    x = mk (rep x) := (mk_rep_eq).symm
    _ = mk (rep y) := Quotient.sound hequiv
    _ = y := mk_rep_eq

/-- Every `ProdNum` whose representative is `brak xs` equals `mk (brak xs)`. -/
lemma eq_mk_brak_of_rep {x : ProdNum} {xs : List PreProdNum} (h : x.rep = PreProdNum.brak xs) :
    x = mk (PreProdNum.brak xs) := by
  conv_lhs => rw [← mk_rep_eq (q := x), h]

/-! ### Lifting API

  Every ProdNum operation `F` is defined via `Quotient.liftOn₂`, so `F (mk a) (mk b) = mk (f a b)`
  holds definitionally (proved by `rfl`). The `lift_eq₁/₂/₃` lemmas encapsulate the full
  `Quotient.ind + Eq.trans + congr_arg mk` pattern, making every ProdNum lifting theorem a one-liner. -/

/-- Lift a unary ProdNum equation from a PreProdNum equation. -/
lemma lift_eq₁ {F G : ProdNum → ProdNum} {f g : PreProdNum → PreProdNum}
    (h : ∀ a, f a = g a)
    (hF : ∀ a, F (mk a) = mk (f a) := by intro _; rfl)
    (hG : ∀ a, G (mk a) = mk (g a) := by intro _; rfl) :
    ∀ x, F x = G x :=
  Quotient.ind (fun a => (hF a).trans ((congr_arg mk (h a)).trans (hG a).symm))

/-- Lift a binary ProdNum equation from a PreProdNum equation. -/
lemma lift_eq₂ {F G : ProdNum → ProdNum → ProdNum} {f g : PreProdNum → PreProdNum → PreProdNum}
    (h : ∀ a b, f a b = g a b)
    (hF : ∀ a b, F (mk a) (mk b) = mk (f a b) := by intro _ _; rfl)
    (hG : ∀ a b, G (mk a) (mk b) = mk (g a b) := by intro _ _; rfl) :
    ∀ x y, F x y = G x y :=
  fun x y => Quotient.ind₂ (fun a b =>
    (hF a b).trans ((congr_arg mk (h a b)).trans (hG a b).symm)) x y

/-- Lift a ternary ProdNum equation from a PreProdNum equation. -/
lemma lift_eq₃ {F G : ProdNum → ProdNum → ProdNum → ProdNum}
    {f g : PreProdNum → PreProdNum → PreProdNum → PreProdNum}
    (h : ∀ a b c, f a b c = g a b c)
    (hF : ∀ a b c, F (mk a) (mk b) (mk c) = mk (f a b c) := by intro _ _ _; rfl)
    (hG : ∀ a b c, G (mk a) (mk b) (mk c) = mk (g a b c) := by intro _ _ _; rfl) :
    ∀ x y z, F x y z = G x y z :=
  fun x y z => Quotient.inductionOn₃ x y z (fun a b c =>
    (hF a b c).trans ((congr_arg mk (h a b c)).trans (hG a b c).symm))

end ProdNum
