import Prod.quot_defs
import Prod.prune_basic
import Mathlib.Data.Prod.Basic
import Mathlib.Order.Defs.PartialOrder

namespace RawProd

-- couldnt get inductive to work so doing good old def instead


-- make literally ∀ rather than .Forall
def pleq_raw : (RawProd ) → (RawProd) →  Prop
  | zero, _        => True
  | brak _, zero        => False
  | brak xs, brak ys => ∀ xy ∈ (pad xs ys), (pleq_raw xy.1 xy.2)
termination_by x y => x.size + y.size
decreasing_by
  sorry


scoped infixl:50 " ⊑ " => pleq_raw


lemma zero_pleq {x : RawProd} : zero ⊑ x := by
  simp only [pleq_raw]

lemma pleq_zero_eq_zero {x : RawProd} (hleq : x ⊑ zero) : x = zero := by
  cases x with
  | zero => rfl
  | brak xs  => simp_all only [pleq_raw]

lemma nil_pleq_brak {xs : List RawProd} : brak [] ⊑ brak xs := by
  induction xs with
  | nil => simp only [pleq_raw, pad_nil, List.length_nil, List.replicate_zero, List.zip_nil_right, List.not_mem_nil, IsEmpty.forall_iff, implies_true]
  | cons x xx ih =>
    --simp_all only [pleq_raw, nil_pad, List.length_cons]
    simp_all only [pleq_raw, Prod.forall, pad_nil_cons, List.mem_cons, forall_eq_or_imp, Prod.mk.eta, implies_true, and_self]

lemma brak_pleq_brak (xs ys : List RawProd) (hl: brak xs ⊑ brak ys) : (∀ p ∈ pad xs ys, p.1 ⊑ p.2) := by simp only [pleq_raw, Prod.forall] at hl; intro p hp; exact hl p.1 p.2 hp

lemma cons_pleq_cons_iff {x y : RawProd} {xs ys : List RawProd} : brak (x::xs) ⊑ brak (y::ys) ↔  x ⊑ y ∧ brak xs ⊑ brak ys := by
  constructor
  . simp_all only [pleq_raw, pad_cons_cons, List.mem_cons, forall_eq_or_imp, Prod.forall, Prod.mk.eta, implies_true, and_self]
  . intro hs
    simp only [pleq_raw, pad_cons_cons, List.mem_cons, forall_eq_or_imp, Prod.forall]
    constructor
    . exact hs.1
    . simp only [pleq_raw, Prod.forall] at hs
      exact hs.2


lemma pleq_head_tail_imp_pleq_cons {x y : RawProd} {xs ys : List RawProd } (h_head : x ⊑ y) (h_tail: brak xs ⊑ brak ys ) : brak (x::xs) ⊑ brak (y::ys) := by
  simp_all only [pleq_raw, Prod.forall, pad_cons_cons, List.mem_cons, forall_eq_or_imp, Prod.mk.eta,
    implies_true, and_self]


lemma brak_pleq_nil_eq_replicate_zero {xs : List RawProd} (hleq: brak xs ⊑ brak []) : xs = List.replicate (xs.length) zero := by
  induction xs with
  | nil => simp only [List.length_nil, List.replicate_zero]
  | cons x xs ih =>
    simp only [pleq_raw, pad_cons_nil, List.mem_cons, forall_eq_or_imp, Prod.forall] at hleq
    simp only [List.length_cons, List.replicate_succ, List.cons.injEq]
    obtain ⟨hx, hxs⟩ := hleq
    apply pleq_zero_eq_zero at hx
    simp_all only [pad_nil, true_and]
    simp only [pleq_raw, pad_nil] at ih
    --exact ih hxs
    apply ih
    intro xy
    exact hxs xy.1 xy.2


lemma replicate_zero_pleq_brak {n: ℕ } (xs : List RawProd): brak (List.replicate n zero) ⊑ brak xs := by
  simp only [pleq_raw, Prod.forall]
  intro x y ihxy
  apply pad_cases_strong at ihxy

  suffices hx_zero : x = zero by rw [hx_zero]; exact zero_pleq

  cases ihxy
  case inl hl =>
    apply List.of_mem_zip at hl
    simp [List.mem_replicate] at hl
    exact hl.1.2
  case inr hmid =>
    cases hmid
    case inl hm =>
      simp_all only
    case inr hr =>
      simp [List.mem_replicate] at hr
      exact hr.1.2


lemma brak_pleq_replicate_zero_eq_replicate_zero {xs : List RawProd} (hpleq: ∃ n, brak xs ⊑ brak (List.replicate n zero)) : xs = List.replicate xs.length zero := by
  induction xs with
  | nil => simp only [List.length_nil, List.replicate_zero]
  | cons x xs ihx =>
    obtain ⟨n, hn⟩ := hpleq
    induction n with
    | zero => simp only [List.replicate_zero] at hn; exact brak_pleq_nil_eq_replicate_zero hn;
    | succ n ihn =>
      simp only [List.replicate_succ] at hn
      obtain ⟨hx,hxs⟩ := cons_pleq_cons_iff.mp hn
      simp only [List.length_cons, List.replicate_succ, List.cons.injEq]
      constructor
      . exact pleq_zero_eq_zero hx
      . apply ihx; use n





theorem pleq_raw_refl {x : RawProd }: x ⊑ x := by
  revert x
  apply RawProd.induction
  case h_zero => apply zero_pleq
  case h_brak =>
    intro xs ih
    induction xs with
    | nil => apply nil_pleq_brak
    | cons x xs ihxs =>
        simp_all only [List.mem_cons, or_true, implies_true, pleq_raw, Prod.forall, forall_const,
          forall_eq_or_imp, pad_cons_cons, Prod.mk.eta, and_self]


-- have to make answers equiv not equal because of [0,0] ⊑ [] but they arent literally equal
theorem pleq_raw_antisymm {x y : RawProd} (h1 : x ⊑ y) (h2 : y ⊑ x) : x.equiv y := by --: ∀ x y, x ⊑ y → y ⊑ x → x.equiv y := by
  revert h1 h2 x y
  apply RawProd.induction_list₂
  case h_zero_left => intro y hz hy; apply pleq_zero_eq_zero at hy; simp only [equiv, normalize_zero_eq_zero, hy]
  case h_zero_right => intro x hx hz; apply pleq_zero_eq_zero at hx ; simp only [equiv, normalize_zero_eq_zero, hx]
  case h_nil_left =>
    intro ys h1 h2
    rw [brak_pleq_nil_eq_replicate_zero h2]
    simp only [equiv, normalize, List.map_nil, trim_nil_eq_nil, List.map_replicate, normalize_zero_eq_zero, trim_replicate_zero_eq_nil]
  case h_nil_right =>
    intro ys h1 h2
    rw [brak_pleq_nil_eq_replicate_zero h1]
    simp only [equiv, normalize, List.map_nil, trim_nil_eq_nil, List.map_replicate, normalize_zero_eq_zero, trim_replicate_zero_eq_nil]
  case h_cons_cons =>
    intro x y xs ys hx hxs hleq hleq2
    obtain ⟨hxy,h_xs_ys⟩ := cons_pleq_cons_iff.mp hleq
    obtain ⟨hyx,h_ys_xs⟩ := cons_pleq_cons_iff.mp hleq2
    apply cons_equiv_cons
    . exact hx hxy hyx
    . exact hxs h_xs_ys h_ys_xs


theorem pleq_transitivity {x y z : RawProd} (hxy : x ⊑ y) (hyz : y ⊑ z) : x ⊑ z := by
  revert hxy hyz x y z
  apply RawProd.induction_list₃
  case h_zero_left => intro y z h1 h2; exact zero_pleq
  case h_zero_mid => intro x z h1 h2; rw [pleq_zero_eq_zero h1]; exact zero_pleq
  case h_zero_right => intro x y h1 h2; rw [pleq_zero_eq_zero h2] at h1; rw [pleq_zero_eq_zero h1]; exact zero_pleq
  case h_nil_left => simp only [nil_pleq_brak, implies_true]
  case h_nil_mid =>
    intro xs zs hl1 hl2
    rw [brak_pleq_nil_eq_replicate_zero hl1]
    apply replicate_zero_pleq_brak
  case h_nil_right =>
    intro xs zs hl1 hl2
    rw [brak_pleq_nil_eq_replicate_zero hl2] at hl1
    have hxs : xs = List.replicate xs.length zero := by apply brak_pleq_replicate_zero_eq_replicate_zero; use zs.length;
    rw [hxs]
    apply replicate_zero_pleq_brak
  case h_cons_cons_cons =>
      intro x y z xs ys zs hx hxs hl1 hl2
      obtain ⟨hxy, hxsys⟩ := cons_pleq_cons_iff.mp hl1
      obtain ⟨hyz, hyszs⟩ := cons_pleq_cons_iff.mp hl2

      apply pleq_head_tail_imp_pleq_cons
      . exact hx hxy hyz
      . exact hxs hxsys hyszs


theorem pleq_prune_iff { x y : RawProd } : x ⊑ y ↔ (x ⊓ y).equiv x := by
  constructor
  . -- =>
    revert x y
    apply RawProd.induction_list₂
    case h_zero_left => intro _ _ ; rw [zero_prune_eq_zero]; rfl
    case h_zero_right => intro x hx; simp only [prune_zero_eq_zero]; simp only [(pleq_zero_eq_zero hx)]; rfl
    case h_nil_left => intro _ _; rw [nil_prune_eq_nil]; rfl; exact brak_neq_zero
    case h_nil_right =>
      -- use brak xs ⊑ [] to get allzero xs and then...
      intro xs hleq
      have haz := brak_pleq_nil_eq_replicate_zero hleq
      rw [brak_prune_nil_eq_nil, haz]
      simp [equiv, normalize, trim_nil_eq_nil]
      apply trim_eq_nil_iff.mpr
      simp only [allzero, List.length_replicate]
    case h_cons_cons =>
      intro xh yh xt yt h ht hcons
      simp only [cons_prune_cons]
      apply cons_equiv_cons
      . apply h
        exact (cons_pleq_cons_iff.mp hcons).1
      . simp only [prune_raw] at ht
        apply ht
        exact (cons_pleq_cons_iff.mp hcons).2
  . -- <=
    revert x y
    apply RawProd.induction_list₂
    case h_zero_left => intro _ _ ; exact zero_pleq
    case h_zero_right => intro x hx; simp only [prune_zero_eq_zero, equiv, normalize] at hx; rw [← zero_eq_normalize_eq_zero hx]; exact pleq_raw_refl
    case h_nil_left => intro _ _ ; exact nil_pleq_brak
    case h_nil_right =>
      intro xs hprune
      rw [prune_nil_eq_nil] at hprune
      have hxs_az : allzero xs := by
        simp only [equiv, normalize, trim, List.map_nil, List.rdropWhile_nil, brak.injEq, List.nil_eq, List.rdropWhile_eq_nil_iff, List.mem_map, beq_iff_eq, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂] at hprune
        simp only [allzero_iff]
        intro x hin
        have hn := hprune x hin
        exact (zero_eq_normalize_eq_zero hn.symm)
      simp [allzero] at hxs_az
      rw [hxs_az]
      simp only [replicate_zero_pleq_brak]
      simp only [ne_eq, brak_neq_zero, not_false_eq_true]
    case h_cons_cons =>
      intro xh yh xt yt hh ht hcons
      simp only [cons_prune_cons] at hcons
      obtain ⟨hl, hr⟩ := cons_equiv_cons_backwards hcons
      apply cons_pleq_cons_iff.mpr
      simp only [prune_raw] at ht
      exact ⟨hh hl, ht hr⟩


end RawProd

namespace QProd


def pleq (x y : QProd) : Prop :=
  RawProd.pleq_raw (rep x) (rep y)


scoped infixl:50 " ⊑ " => pleq


lemma pleq_refl {x : QProd } : x ⊑ x := by
  dsimp only [pleq]
  apply RawProd.pleq_raw_refl


theorem pleq_antisymm {x y : QProd} (hxy : x ⊑ y) (hyx : y ⊑ x) : x = y := by
  dsimp only [pleq] at hxy hyx
  have hequiv : x.rep.equiv y.rep := RawProd.pleq_raw_antisymm hxy hyx
  exact rep_equiv_eq hequiv


theorem pleq_transitivity {x y z : QProd } (hxy : x ⊑ y) (hyz : y ⊑ z) : x ⊑ z := by
  simp_all only [pleq]
  exact RawProd.pleq_transitivity hxy hyz



instance : PartialOrder QProd where
  le := pleq
  le_refl := @pleq_refl
  le_trans := @pleq_transitivity
  le_antisymm  := @pleq_antisymm




end QProd
