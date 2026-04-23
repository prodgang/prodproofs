import Prod.quot_defs
import Prod.prune_basic
import Prod.bij
import Mathlib.Data.Prod.Basic
import Mathlib.Order.Defs.PartialOrder

namespace RawProd

mutual
  def pleq_raw : RawProd → RawProd → Prop
    | brak xs, brak ys => pleq_list xs ys
    | zero, _ => True
    | _, zero => False

  def pleq_list : List RawProd → List RawProd → Prop
    | [], _ => True
    | x :: xs, [] => allzero (x :: xs)
    | x :: xs, y :: ys => (pleq_raw x y) ∧ pleq_list xs ys
end


scoped infixl:50 " ⊑ " => pleq_raw


lemma zero_pleq {x : RawProd} : zero ⊑ x := by
  simp only [pleq_raw]

lemma pleq_zero_eq_zero {x : RawProd} (hleq : x ⊑ zero) : x = zero := by
  cases x with
  | zero => rfl
  | brak xs  => simp_all only [pleq_raw]

@[simp]
lemma nil_pleq_list_brak {xs : List RawProd} : pleq_list [] xs := by
  simp only [pleq_list]

lemma nil_pleq_brak {xs : List RawProd} : nil ⊑ brak xs := by
  induction xs with
  | nil => simp only [pleq_raw, nil_pleq_list_brak]
  | cons x xx ih =>
    simp_all only [pleq_raw, nil_pleq_list_brak]

lemma cons_pleq_cons_iff {x y : RawProd} {xs ys : List RawProd} : brak (x::xs) ⊑ brak (y::ys) ↔  x ⊑ y ∧ brak xs ⊑ brak ys := by
  constructor
  . simp_all only [pleq_raw, pleq_list, and_self, implies_true]
  . intro hs
    simp only [pleq_raw, pleq_list]
    constructor
    . exact hs.1
    . simp only [pleq_raw] at hs
      exact hs.2


lemma pleq_head_tail_imp_pleq_cons {x y : RawProd} {xs ys : List RawProd } (h_head : x ⊑ y) (h_tail: brak xs ⊑ brak ys ) : brak (x::xs) ⊑ brak (y::ys) := by
  simp_all only [pleq_raw, pleq_list, and_self]


-- lemma brak_pleq_nil_allzero {xs : List RawProd} (hleq: brak xs ⊑ brak []) : allzero xs := by
--   cases xs with
--   | nil => rfl
--   | cons x xs =>
--     simp only [pleq_raw, pleq_list] at hleq
--     exact hleq




lemma replicate_zero_pleq_brak {n: ℕ } (xs : List RawProd): brak (List.replicate n zero) ⊑ brak xs := by
  simp only [pleq_raw]
  induction n generalizing xs with
  | zero => simp only [List.replicate_zero, pleq_list]
  | succ n ih =>
    cases xs with
    | nil =>
      simp only [List.replicate_succ, pleq_list, allzero, List.length_cons, List.length_replicate]
    | cons y ys =>
      simp only [List.replicate_succ, pleq_list, zero_pleq, true_and]
      exact ih ys

lemma brak_pleq_nil_iff_allzero {xs : List RawProd} : brak xs ⊑ nil ↔ allzero xs := by
  constructor
  . intro hleq
    cases xs with
    | nil => rfl
    | cons x xs =>
      simp only [pleq_raw, pleq_list] at hleq
      exact hleq
  . intro h
    rw [allzero] at h
    rw [h]
    simp only [replicate_zero_pleq_brak]


-- Consequence of brak_pleq_nil_iff_allzero: every x ⊑ nil is zero or a brak with allzero list.
-- Used in shallow.lean to case-split on components.
lemma pleq_nil_cases {x : RawProd} (h : x ⊑ nil) :
    x = zero ∨ ∃ ys, x = brak ys ∧ allzero ys := by
    cases x with
    | zero => left; rfl
    | brak xs => right; use xs; exact ⟨rfl, brak_pleq_nil_iff_allzero.mp h⟩
-- cases x: zero → left; brak xs → right via brak_pleq_nil_iff_allzero

lemma nil_pleq_iff_ne_zero {y : RawProd} : nil ⊑ y ↔ y ≠ zero := by
  cases y with
  | zero => simp only [pleq_raw, ne_eq, not_true_eq_false]
  | brak ys => exact ⟨fun _ => brak_neq_zero, fun _ => nil_pleq_brak⟩

lemma pleq_nil_equiv_nil {x : RawProd} (h : x ⊑ nil) (hne : x ≠ zero) : x.equiv nil := by
  rcases pleq_nil_cases h with rfl | ⟨ys, rfl, haz⟩
  · exact absurd rfl hne
  · exact brak_equiv_nil_iff_allzero.mpr haz

lemma replicate_nil_pleq_iff (xs : List RawProd) (j : ℕ) :
    brak (List.replicate j zero ++ [nil]) ⊑ brak xs ↔ get xs j ≠ RawProd.zero := by
  induction j generalizing xs with
  | zero =>
    simp only [List.replicate_zero, List.nil_append]
    cases xs with
    | nil =>
      simp only [get_nil, ne_eq, not_true, iff_false]; intro h
      exact absurd (allzero_iff.mp (brak_pleq_nil_iff_allzero.mp h) nil (by simp only [List.mem_cons, List.not_mem_nil, or_false])) brak_neq_zero
    | cons xh xt =>
      rw [cons_pleq_cons_iff]; simp only [get_cons_zero]
      exact ⟨fun ⟨h, _⟩ => nil_pleq_iff_ne_zero.mp h,
             fun h => ⟨nil_pleq_iff_ne_zero.mpr h, nil_pleq_brak⟩⟩
  | succ n ih =>
    cases xs with
    | nil =>
      simp only [get_nil, ne_eq, not_true, iff_false]; intro h
      have h_nil : nil ∈ List.replicate (n + 1) zero ++ [nil] := by apply List.mem_append.mpr ; right; apply List.mem_singleton.mpr; rfl
      exact absurd (allzero_iff.mp (brak_pleq_nil_iff_allzero.mp h) nil (by simp only [h_nil])) brak_neq_zero
    | cons xh xt =>
      rw [List.replicate_succ, List.cons_append, cons_pleq_cons_iff]; simp only [get_cons_succ]
      exact ⟨fun ⟨_, ht⟩ => (ih xt).mp ht, fun h => ⟨zero_pleq, (ih xt).mpr h⟩⟩

-- this seems like a clumsy lemma 0 why not use allzero?
lemma brak_pleq_replicate_zero_eq_replicate_zero {xs : List RawProd} (hpleq: ∃ n, brak xs ⊑ brak (List.replicate n zero)) : xs = List.replicate xs.length zero := by
  induction xs with
  | nil => simp only [List.length_nil, List.replicate_zero]
  | cons x xs ihx =>
    obtain ⟨n, hn⟩ := hpleq
    induction n with
    | zero => simp only [List.replicate_zero] at hn; exact brak_pleq_nil_iff_allzero.mp hn;
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
        simp_all only [List.mem_cons, or_true, implies_true, pleq_raw, forall_const,
          forall_eq_or_imp, pleq_list, and_self]


-- have to make answers equiv not equal because of [0,0] ⊑ [] but they arent literally equal
theorem pleq_raw_antisymm {x y : RawProd} (h1 : x ⊑ y) (h2 : y ⊑ x) : x.equiv y := by --: ∀ x y, x ⊑ y → y ⊑ x → x.equiv y := by
  revert h1 h2 x y
  apply RawProd.induction_list₂
  case h_zero_left => intro y hz hy; apply pleq_zero_eq_zero at hy; simp only [equiv, normalize_zero_eq_zero, hy]
  case h_zero_right => intro x hx hz; apply pleq_zero_eq_zero at hx ; simp only [equiv, normalize_zero_eq_zero, hx]
  case h_nil_left =>
    intro ys h1 h2
    rw [brak_pleq_nil_iff_allzero.mp h2]
    simp only [equiv, normalize, List.map_nil, trim_nil_eq_nil, List.map_replicate, normalize_zero_eq_zero, trim_replicate_zero_eq_nil]
  case h_nil_right =>
    intro ys h1 h2
    rw [brak_pleq_nil_iff_allzero.mp h1]
    simp only [equiv, normalize, List.map_nil, trim_nil_eq_nil, List.map_replicate, normalize_zero_eq_zero, trim_replicate_zero_eq_nil]
  case h_cons_cons =>
    intro x y xs ys hx hxs hleq hleq2
    obtain ⟨hxy,h_xs_ys⟩ := cons_pleq_cons_iff.mp hleq
    obtain ⟨hyx,h_ys_xs⟩ := cons_pleq_cons_iff.mp hleq2
    apply cons_equiv_cons_iff.mp
    constructor
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
    rw [brak_pleq_nil_iff_allzero.mp hl1]
    apply replicate_zero_pleq_brak
  case h_nil_right =>
    intro xs zs hl1 hl2
    rw [brak_pleq_nil_iff_allzero.mp hl2] at hl1
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


theorem pleq_prune_raw_iff { x y : RawProd } : x ⊑ y ↔ (x ⊓ y).equiv x := by
  constructor
  . -- =>
    revert x y
    apply RawProd.induction_list₂
    case h_zero_left => intro _ _ ; rw [zero_prune_eq_zero]; rfl
    case h_zero_right => intro x hx; simp only [prune_zero_eq_zero]; simp only [(pleq_zero_eq_zero hx)]; rfl
    case h_nil_left => intro _ _; rw [nil_prune_nz_eq_nil]; rfl; exact brak_neq_zero
    case h_nil_right =>
      -- use brak xs ⊑ [] to get allzero xs and then...
      intro xs hleq
      have haz := brak_pleq_nil_iff_allzero.mp hleq
      rw [brak_prune_nil_eq_nil, haz]
      simp only [equiv, normalize_nil_eq_nil, normalize, equiv_zero_eq_zero, List.map_replicate, brak.injEq, List.nil_eq]
      apply trim_eq_nil_iff.mpr
      simp only [allzero, List.length_replicate]
    case h_cons_cons =>
      intro xh yh xt yt h ht hcons
      simp only [cons_prune_cons]
      apply cons_equiv_cons_iff.mp; constructor
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
      have hxs_az : allzero xs := nil_equiv_brak_iff_allzero.mp hprune
      simp only [allzero] at hxs_az
      rw [hxs_az]
      exact replicate_zero_pleq_brak []

    case h_cons_cons =>
      intro xh yh xt yt hh ht hcons
      simp only [cons_prune_cons] at hcons
      obtain ⟨hl, hr⟩ := cons_equiv_cons_iff.mpr hcons
      apply cons_pleq_cons_iff.mpr
      simp only [prune_raw] at ht
      exact ⟨hh hl, ht hr⟩


lemma pleq_raw_normalize_right (x y : RawProd) :
    x ⊑ y ↔ x ⊑ normalize y := by
  rw [pleq_prune_raw_iff, pleq_prune_raw_iff]
  have h : (x ⊓ y).equiv (x ⊓ normalize y) :=
    prune_raw_respects_equiv (equiv_refl x) (equiv_symm equiv_of_normalize)
  simp only [equiv] at h ⊢; rw [h]

lemma pleq_raw_normalize_left (x y : RawProd) :
    x ⊑ y ↔ normalize x ⊑ y := by
  rw [pleq_prune_raw_iff, pleq_prune_raw_iff]
  have h : (x ⊓ y).equiv (normalize x ⊓ y) :=
    prune_raw_respects_equiv (equiv_symm equiv_of_normalize) (equiv_refl y)
  simp only [equiv, normalize_idem] at h ⊢; rw [h]


theorem pleq_dvd {x y : RawProd } (hnz: x ≠ zero) (hlq: x ⊑ y ): interp_raw x ∣ interp_raw y := by
  revert x y
  apply induction_list₂
  case h_zero_left => intros; contradiction;
  case h_zero_right => intro x hx hx2; exfalso; exact hx (pleq_zero_eq_zero hx2)
  case h_nil_left => intros; simp only [interp_raw, interp_raw_nil, isUnit_iff_eq_one, IsUnit.dvd]
  case h_nil_right => intro xs hnz hl; have haz :=  brak_pleq_nil_iff_allzero.mp hl; simp only [interp_raw, interp_allzero_eq_one haz, interp_raw_nil, dvd_refl]
  case h_cons_cons =>
    intro x y xs ys h1 h2 h3 h4
    -- turn x | y to x.factorization < y.factorization
    apply (Nat.factorization_prime_le_iff_dvd (interp_list_neq_zero _) (interp_list_neq_zero _)).mp
    intro p hp
    obtain ⟨hxy, hbrak⟩ := cons_pleq_cons_iff.mp h4
    obtain ⟨i, hi⟩ := prime_index hp
    rw [hi]
    -- apply bridge lemma
    rw [factorization_interp_list_zero, factorization_interp_list_zero]
    cases i with
    | zero =>
      -- head, wrangle h1
      simp only [get_cons_zero]
      by_cases hxz : x = zero
      · simp only [hxz, interp_raw_zero, zero_le]
      · have hyz : y ≠ zero := fun h => hxz (pleq_zero_eq_zero (h ▸ hxy))
        have hynz : interp_raw y ≠ 0 := fun h => hyz (interp_raw_eq_zero_eq_zero y h)
        exact Nat.le_of_dvd (by omega) (h1 hxz hxy)
    | succ j =>
      --tail, wrangle h2
      simp only [get_cons_succ]
      have hdvd := h2 brak_neq_zero hbrak
      simp only [interp_raw] at hdvd
      have hle := (Nat.factorization_prime_le_iff_dvd
        (interp_list_neq_zero xs) (interp_list_neq_zero ys)).mpr hdvd (Nat.nth Nat.Prime j) (Nat.prime_nth_prime j)
      rw [← factorization_interp_list_zero j (xs := xs), ← factorization_interp_list_zero j (xs := ys)]
      exact hle

-- Converse of pleq_dvd fails:
--   x = [[[]]] = 2^(2^1) = 4,  y = [[0,[]]] = 2^(2^0 · 3^1) = 2^3 = 8
--   so interp_raw x = 4,  interp_raw y = 8,  4 ∣ 8,  but x ⊄ y.
theorem converse_counterexample :
    let x := brak [brak [nil]]
    let y := brak [brak [zero, nil]]
    interp_raw x = 4 ∧ interp_raw y = 8 ∧ (4 : ℕ) ∣ 8 ∧ ¬ (x ⊑ y) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp only [interp_raw, interp_list, Nat.nth_prime_zero_eq_two]; norm_num
  · simp only [interp_raw, interp_list, Nat.nth_prime_zero_eq_two]; norm_num
  · norm_num
  · intro h
    have : nil ⊑ (zero : RawProd) :=
      (cons_pleq_cons_iff.mp (cons_pleq_cons_iff.mp h).1).1
    simp only [pleq_raw] at this



end RawProd

namespace QProd


def pleq (x y : QProd) : Prop :=
  RawProd.pleq_raw (rep x) (rep y)


scoped infixl:50 " ⊑ " => pleq


lemma pleq_refl (x : QProd) : x ⊑ x := by
  dsimp only [pleq]
  apply RawProd.pleq_raw_refl


theorem pleq_antisymm (x y : QProd) (hxy : x ⊑ y) (hyx : y ⊑ x) : x = y := by
  dsimp only [pleq] at hxy hyx
  have hequiv : x.rep.equiv y.rep := RawProd.pleq_raw_antisymm hxy hyx
  exact rep_equiv_eq hequiv


theorem pleq_transitivity (x y z : QProd) (hxy : x ⊑ y) (hyz : y ⊑ z) : x ⊑ z := by
  simp_all only [pleq]
  exact RawProd.pleq_transitivity hxy hyz


/-- The fundamental bridge: `mk a ⊑ mk b` in QProd iff `a ⊑ b` as raw terms.
    Replaces the need for separate `le_mk_iff` / `mk_le_iff` variants. -/
lemma mk_pleq_mk_iff {a b : RawProd} : (mk a : QProd) ⊑ mk b ↔ RawProd.pleq_raw a b := by
  show RawProd.pleq_raw (RawProd.normalize a) (RawProd.normalize b) ↔ RawProd.pleq_raw a b
  exact (RawProd.pleq_raw_normalize_left a (RawProd.normalize b)).symm.trans
        (RawProd.pleq_raw_normalize_right a b).symm

/-- Lift a unary QProd order statement from a raw `pleq_raw` statement.
    Analogue of `lift_eq₁` for `⊑` instead of `=`.
    Note: uses term-mode `▸` rather than `rw` because `rw` cannot match `mk a` against `⟦a⟧`
    even though they are definitionally equal. -/
lemma lift_pleq₁ {f g : RawProd → RawProd} {F G : QProd → QProd}
    (hF : ∀ a, F (mk a) = mk (f a) := by intro _; rfl)
    (hG : ∀ a, G (mk a) = mk (g a) := by intro _; rfl)
    (h : ∀ a, RawProd.pleq_raw (f a) (g a)) :
    ∀ x, F x ⊑ G x :=
  Quotient.ind (fun a => hF a ▸ hG a ▸ mk_pleq_mk_iff.mpr (h a))

/-- Lift a binary QProd order statement from a raw `pleq_raw` statement.
    Analogue of `lift_eq₂` for `⊑` instead of `=`.
    Note: uses term-mode `▸` rather than `rw` — see `lift_pleq₁`. -/
lemma lift_pleq₂ {f g : RawProd → RawProd → RawProd} {F G : QProd → QProd → QProd}
    (hF : ∀ a b, F (mk a) (mk b) = mk (f a b) := by intro _ _; rfl)
    (hG : ∀ a b, G (mk a) (mk b) = mk (g a b) := by intro _ _; rfl)
    (h : ∀ a b, RawProd.pleq_raw (f a b) (g a b)) :
    ∀ x y, F x y ⊑ G x y :=
  fun x y => Quotient.ind₂ (fun a b => hF a b ▸ hG a b ▸ mk_pleq_mk_iff.mpr (h a b)) x y


-- instance : PartialOrder QProd where
--   le := pleq
--   le_refl := pleq_refl
--   le_trans := pleq_transitivity
--   le_antisymm := pleq_antisymm


lemma pleq_prune_iff {x y : QProd} : x ⊑ y ↔ x ⊓ y = x := by
  have hxy : x ⊓ y = mk (x.rep ⊓ y.rep) := by
    conv_lhs => rw [← mk_rep_eq (q := x), ← mk_rep_eq (q := y)]
    exact prune_mk_mk x.rep y.rep
  constructor
  · intro h
    rw [hxy]; exact (Quotient.sound (RawProd.pleq_prune_raw_iff.mp h)).trans mk_rep_eq
  · intro h
    apply RawProd.pleq_prune_raw_iff.mpr
    rw [hxy] at h; exact Quotient.exact (h.trans mk_rep_eq.symm)


end QProd
