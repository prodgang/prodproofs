import Prod.quot_defs
import Mathlib.Data.Prod.Basic

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


lemma zero_pleq (x : RawProd) : zero ⊑ x := by
  simp only [pleq_raw]

lemma pleq_zero_eq_zero {x : RawProd} (hleq : x ⊑ zero) : x = zero := by
  cases x with
  | zero => rfl
  | brak xs  => simp_all only [pleq_raw]

lemma nil_pleq_brak (xs : List RawProd) : brak [] ⊑ brak xs := by
  induction xs with
  | nil => simp only [pleq_raw, pad_nil, List.length_nil, List.replicate_zero, List.zip_nil_right, List.not_mem_nil, IsEmpty.forall_iff, implies_true]
  | cons x xx ih =>
    --simp_all only [pleq_raw, nil_pad, List.length_cons]
    simp_all only [pleq_raw, Prod.forall, pad_nil_cons, List.mem_cons, forall_eq_or_imp, Prod.mk.eta, implies_true, and_self]

lemma brak_pleq_brak (xs ys : List RawProd) (hl: brak xs ⊑ brak ys) : (∀ p ∈ pad xs ys, p.1 ⊑ p.2) := by simp only [pleq_raw, Prod.forall] at hl; intro p hp; exact hl p.1 p.2 hp

lemma cons_pleq_cons {x y : RawProd} {xs ys : List RawProd} (hp: brak (x::xs) ⊑ brak (y::ys)) : x ⊑ y ∧ brak xs ⊑ brak ys := by
  simp_all only [pleq_raw, pad_cons_cons, List.mem_cons, forall_eq_or_imp, Prod.forall, Prod.mk.eta,
    implies_true, and_self]

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

  suffices hx_zero : x = zero by rw [hx_zero]; exact zero_pleq y

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
      obtain ⟨hx,hxs⟩ := cons_pleq_cons hn
      simp only [List.length_cons, List.replicate_succ, List.cons.injEq]
      constructor
      . exact pleq_zero_eq_zero hx
      . apply ihx; use n





theorem pleq_raw_refl: ∀ x, x ⊑ x := by
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
-- set_option diagnostics true
-- set_option diagnostics.threshold 0
theorem pleq_raw_antisymm : ∀ x y, x ⊑ y → y ⊑ x → x.equiv y := by
  apply RawProd.strong_induction₂
  case h_zero_left => intro y hz hy; apply pleq_zero_eq_zero at hy; simp only [equiv, normalize_zero_eq_zero, hy]
  case h_zero_right => intro x hx hz; apply pleq_zero_eq_zero at hx ; simp only [equiv, normalize_zero_eq_zero, hx]
  case h_brak_brak =>
    intro xs ys ih hxs hys
    induction xs generalizing ys with
    | nil => simp only [List.not_mem_nil, IsEmpty.forall_iff, implies_true] at ih
             rw [brak_pleq_nil_eq_replicate_zero hys]
             simp only [equiv, normalize, List.map_nil, trim_nil_eq_nil, List.map_replicate, normalize_zero_eq_zero, trim_replicate_zero_eq_nil]
    | cons x xs ihxs =>
      cases ys with
      | nil =>  simp only [List.not_mem_nil, IsEmpty.forall_iff, implies_true] at ih
                rw [brak_pleq_nil_eq_replicate_zero hxs]
                simp only [equiv, normalize, List.map_nil, trim_nil_eq_nil, List.map_replicate, normalize_zero_eq_zero, trim_replicate_zero_eq_nil]
      | cons y ys =>

        obtain ⟨hxy,h_xs_ys⟩ := cons_pleq_cons hxs
        obtain ⟨hyx,h_ys_xs⟩ := cons_pleq_cons hys
        apply cons_equiv_cons
        . exact ih x (List.mem_cons_self) y (List.mem_cons_self) hxy hyx
        . apply ihxs
          . intros x' hx' y' hy' hx'y' hy'x'; exact ih x' (List.mem_cons_of_mem x hx') y' (List.mem_cons_of_mem y hy') hx'y' hy'x'
          . exact h_xs_ys
          . exact h_ys_xs


-- theorem pleq_transitivity_nifty : ∀ x y z, x ⊑ y → y ⊑ z → x ⊑ z := by
--   apply RawProd.strong_induction₃
--   case h_zero_left => intro y z h1 h2; exact zero_pleq z
--   case h_zero_mid => intro x z h1 h2; rw [pleq_zero_eq_zero h1]; exact zero_pleq z
--   case h_zero_right => intro x y h1 h2; rw [pleq_zero_eq_zero h2] at h1; rw [pleq_zero_eq_zero h1]; exact zero_pleq zero
--   case h_brak_brak_brak =>
--     intro xs ys zs ih hl1 hl2
--     simp only [pleq_raw]
--     let p := pad xs zs
--     have hp : p = pad xs zs := rfl
--     rw [← hp]

--     induction (p) generalizing hp with
--     | nil => simp only [List.not_mem_nil, IsEmpty.forall_iff, implies_true]
--     | cons ph pt ihpt => sorry --hp doesnt generalise :(
--     -- really want ot use apply pad_cases rather than doing cases on xs ys zs...
--     -- cases p

theorem pleq_transitivity : ∀ x y z, x ⊑ y → y ⊑ z → x ⊑ z := by
  apply RawProd.strong_induction₃
  case h_zero_left => intro y z h1 h2; exact zero_pleq z
  case h_zero_mid => intro x z h1 h2; rw [pleq_zero_eq_zero h1]; exact zero_pleq z
  case h_zero_right => intro x y h1 h2; rw [pleq_zero_eq_zero h2] at h1; rw [pleq_zero_eq_zero h1]; exact zero_pleq zero
  case h_brak_brak_brak =>
      intro xs ys zs ih hl1 hl2
      induction xs generalizing ys zs
      . -- [] ys zs
        simp only [nil_pleq_brak]
      . cases ys <;> cases zs
        . -- xs [] zs
          rename_i x xs _
          apply brak_pleq_nil_eq_replicate_zero at hl1
          rw [hl1]
          apply replicate_zero_pleq_brak
        . -- xs [] ys
          rename_i x xs z zs _
          apply brak_pleq_nil_eq_replicate_zero at hl1
          rw [hl1]
          apply replicate_zero_pleq_brak
        . -- xs ys []
          rename_i x xs _ y ys
          apply brak_pleq_nil_eq_replicate_zero at hl2
          have hys : y::ys = List.replicate (ys.length + 1) zero := by simp only [List.length_cons] at hl2; exact hl2;
          have hxs : x::xs = List.replicate (xs.length + 1) zero := by rw [hys] at hl1; apply brak_pleq_replicate_zero_eq_replicate_zero; use ys.length + 1;
          rw [hxs]
          apply replicate_zero_pleq_brak
        . -- xs ys zs (the real deal)
          rename_i x xs ihx y ys z zs

          obtain ⟨hxy, hxsys⟩ := cons_pleq_cons hl1
          obtain ⟨hyz, hyszs⟩ := cons_pleq_cons hl2

          apply pleq_head_tail_imp_pleq_cons
          . exact ih x (List.mem_cons_self) y (List.mem_cons_self) z (List.mem_cons_self) hxy hyz
          . apply ihx ys zs
            . intros x' hx' y' hy' z' hz'; apply ih x' (List.mem_cons_of_mem x hx') y' (List.mem_cons_of_mem y hy') z' (List.mem_cons_of_mem z hz')
            . exact hxsys
            . exact hyszs



end RawProd
