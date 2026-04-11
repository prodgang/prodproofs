import Prod.poset
import Prod.lattice
import Mathlib.Order.Sublattice
import Mathlib.Order.Heyting.Basic

/-!
## Heyting algebra on principal downsets

`instance (x : QProd) : HeytingAlgebra (Downset x)`
where `Downset x = {y : QProd | y ≤ x}`.
-/

namespace RawProd

mutual
  /-- Heyting implication relative to bound `x`:
      `himp_raw x a b` is the greatest `c ⊑ x` such that `a ⊓ c ⊑ b`. -/
  def himp_raw : RawProd → RawProd → RawProd → RawProd
    | zero,    _,       _       => zero
    | x,       zero,    _       => x
    | _,       _,       zero    => zero
    | brak xs, brak as, brak bs => brak (himp_list xs as bs)

  /-- Componentwise himp on lists: recurse on the bound list,
      reading head elements of `as` and `bs` via `get`. -/
  def himp_list : List RawProd → List RawProd → List RawProd → List RawProd
    | [],       _,  _  => []
    | x :: xs,  as, bs =>
        himp_raw x (get as 0) (get bs 0) :: himp_list xs as.tail bs.tail
end

private lemma get_tail (xs : List RawProd) (i : ℕ) : get xs (i + 1) = get xs.tail i := by
  cases xs with
  | nil => simp only [get_nil, List.tail_nil]
  | cons _ _ => simp only [get_cons_succ, List.tail_cons]


/-- `get (himp_list xs as bs) i = himp_raw (get xs i) (get as i) (get bs i)`.
    Key helper: reduces all subsequent proofs to scalar `himp_raw` calls. -/
lemma get_himp_list (xs as bs : List RawProd) (i : ℕ) :
    get (himp_list xs as bs) i = himp_raw (get xs i) (get as i) (get bs i) := by
  induction xs generalizing as bs i with
  | nil =>
    simp only [himp_list, get_nil, himp_raw]
  | cons xh xt ih =>
    cases i with
    | zero =>
      simp only [himp_list, get_cons_zero]
    | succ j =>
      simp only [himp_list, get_tail]
      exact ih as.tail bs.tail j

/-- `himp_raw x a b ⊑ x`: the result is always bounded by `x`. -/
lemma himp_raw_pleq_bound (x a b : RawProd) : himp_raw x a b ⊑ x := by
  revert x a b
  apply induction
  case h_zero => intro a b; simp only [himp_raw, pleq_raw_refl]
  case h_brak =>
    intro xs hx a b
    cases a
    · simp only [himp_raw, pleq_raw_refl]
    · rename_i as
      cases b
      · simp only [himp_raw, zero_pleq]
      · rename_i bs
        simp only [himp_raw]
        induction xs generalizing as bs with
        | nil => simp only [himp_list, nil_pleq_brak]
        | cons xh xt ih =>
          simp only [pleq_raw, himp_list, pleq_list] at ih ⊢
          exact ⟨hx xh (List.mem_cons.mpr (.inl rfl)) _ _,
                 ih (fun x hxt a b => hx x (List.mem_cons_of_mem xh hxt) a b) as.tail bs.tail⟩


lemma pleq_raw_normalize_right (x y : RawProd) :
    x ⊑ y ↔ x ⊑ normalize y := by
  rw [pleq_prune_raw_iff, pleq_prune_raw_iff]
  have h : (x ⊓ y).equiv (x ⊓ normalize y) :=
    prune_raw_respects_equiv (equiv_refl x) (equiv_symm equiv_of_normalize)
  constructor
  · intro he; exact equiv_trans (equiv_symm h) he
  · intro he; exact equiv_trans h he

lemma pleq_raw_normalize_left (x y : RawProd) :
    x ⊑ y ↔ normalize x ⊑ y := by
  rw [pleq_prune_raw_iff, pleq_prune_raw_iff]
  have h : (x ⊓ y).equiv (normalize x ⊓ y) :=
    prune_raw_respects_equiv (equiv_symm equiv_of_normalize) (equiv_refl y)
  simp only [equiv, normalize_idem] at h ⊢
  constructor
  · intro he; exact h.symm.trans he
  · intro he; exact h.trans he

/-- Core Heyting adjunction: `a ⊑ x → (a ⊑ himp_raw x b c ↔ a ⊓ b ⊑ c)`. -/
lemma himp_raw_adjunction {x a b c : RawProd} (ha : a ⊑ x) :
    a ⊑ himp_raw x b c ↔ a ⊓ b ⊑ c := by
  -- Generalise over a b c before induction so the IH is ∀ a b c, not specialised.
  suffices key : ∀ y a b c : RawProd, a ⊑ y → (a ⊑ himp_raw y b c ↔ a ⊓ b ⊑ c) from key x a b c ha
  intro y
  induction y using RawProd.induction_list
  case h_zero =>
    intro a b c ha
    rw [pleq_zero_eq_zero ha]
    simp only [himp_raw, zero_pleq, zero_prune_eq_zero]
  case h_nil =>
    intro a b c ha
    cases a <;> cases b <;> cases c
    all_goals simp only [himp_raw, zero_pleq, prune_zero_eq_zero, zero_prune_eq_zero,
      iff_true]
    · exact ha
    · exact ha
    · rename_i as bs
      constructor
      · intro h; simp only [pleq_raw] at h
      · intro h; exact absurd (pleq_zero_eq_zero h) (brak_prune_brak_neq_zero _ _)
    · rename_i as bs cs
      constructor
      · intro _
        have haz := brak_pleq_nil_iff_allzero.mp ha
        suffices h : brak as ⊓ brak bs ⊑ brak [] from pleq_transitivity h nil_pleq_brak
        rw [allzero_prune_eq_replicate haz]
        exact replicate_zero_pleq_brak _
      · intro _; exact ha
  case h_cons xh xs ih_head ih_tail =>
    intro a b c ha
    cases a with
    | zero => simp only [himp_raw, zero_pleq, zero_prune_eq_zero]
    | brak as =>
      cases b with
      | zero => simp only [himp_raw, prune_zero_eq_zero, zero_pleq, iff_true]; exact ha
      | brak bs =>
        cases c with
        | zero =>
          simp only [himp_raw]
          constructor
          · intro h; simp only [pleq_raw] at h
          · intro h; exact absurd (pleq_zero_eq_zero h) (brak_prune_brak_neq_zero _ _)
        | brak cs =>
          simp only [himp_raw, himp_list]
          cases as with
          | nil =>
            simp only [nil_pleq_brak, ne_eq, brak_neq_zero, not_false_eq_true, nil_prune_nz_eq_nil]
          | cons ah at_ =>
            obtain ⟨ha_head, ha_tail⟩ := cons_pleq_cons_iff.mp ha
            have iff_head := ih_head ah (get bs 0) (get cs 0) ha_head
            have iff_tail := ih_tail (brak at_) (brak bs.tail) (brak cs.tail) ha_tail
            cases bs with
            | nil =>
              constructor
              . intro h
                exact nil_pleq_brak
              . intro _
                apply cons_pleq_cons_iff.mpr
                simp only [get_nil, prune_zero_eq_zero, zero_pleq, iff_true] at iff_head
                simp only [List.tail_nil, ne_eq, brak_neq_zero, not_false_eq_true, prune_nil_nz_eq_nil, nil_pleq_brak, iff_true] at iff_tail
                exact ⟨iff_head, iff_tail⟩
            | cons bh bt =>
              cases cs with
              | nil =>
                rw [cons_prune_cons]
                constructor
                · intro h
                  obtain ⟨hh, ht⟩ := cons_pleq_cons_iff.mp h
                  rw [brak_pleq_nil_iff_allzero, allzero, List.length_cons,
                      List.replicate_succ, List.cons.injEq]
                  exact ⟨pleq_zero_eq_zero (iff_head.mp hh), brak_pleq_nil_iff_allzero.mp (iff_tail.mp ht)⟩
                · intro h
                  rw [brak_pleq_nil_iff_allzero, allzero, List.length_cons,
                      List.replicate_succ, List.cons.injEq] at h
                  obtain ⟨hh, ht⟩ := h
                  exact cons_pleq_cons_iff.mpr ⟨iff_head.mpr (hh ▸ zero_pleq),
                                                 iff_tail.mpr (brak_pleq_nil_iff_allzero.mpr ht)⟩
              | cons ch ct =>
                simp only [get_cons_zero, List.tail_cons]
                rw [cons_prune_cons]
                constructor
                · intro h
                  obtain ⟨hh, ht⟩ := cons_pleq_cons_iff.mp h
                  exact cons_pleq_cons_iff.mpr ⟨iff_head.mp hh, iff_tail.mp ht⟩
                · intro h
                  obtain ⟨hh, ht⟩ := cons_pleq_cons_iff.mp h
                  exact cons_pleq_cons_iff.mpr ⟨iff_head.mpr hh, iff_tail.mpr ht⟩

end RawProd

namespace QProd

open RawProd

lemma pleq_iff_le {x y : QProd} : x ⊑ y ↔ x ≤ y :=
  pleq_prune_iff.trans inf_eq_left

lemma zero_le (y : QProd) : QProd.zero ≤ y :=
  pleq_iff_le.mp (by
    show RawProd.pleq_raw (rep QProd.zero) (rep y)
    have : rep QProd.zero = RawProd.zero := by
      show RawProd.normalize RawProd.zero = RawProd.zero
      exact RawProd.normalize_zero_eq_zero
    rw [this]; exact RawProd.zero_pleq)

@[reducible]
def downsetSublattice (x : QProd) : Sublattice QProd where
  carrier    := {y | y ≤ x}
  supClosed' := fun _ ha _ hb => Set.mem_setOf.mpr (sup_le ha hb)
  infClosed' := fun _ ha _ _ => Set.mem_setOf.mpr (inf_le_left.trans ha)


lemma pleq_iff_downset {x y : QProd} : x ≤ y ↔ x ∈ y.downsetSublattice := by
  simp only [Sublattice.mem_mk, Set.mem_setOf_eq]


/-- The principal downset `{y : QProd | y ≤ x}` as a type. -/
abbrev Downset (x : QProd) : Type := ↥(downsetSublattice x)

instance (x : QProd) : Lattice (Downset x) := inferInstance

instance (x : QProd) : DistribLattice (Downset x) :=
  DistribLattice.ofInfSupLe fun a b c => by
    apply le_of_eq; apply Subtype.ext
    exact QProd.distrib a.val b.val c.val

instance (x : QProd) : BoundedOrder (Downset x) where
  top    := ⟨x, pleq_iff_downset.mp (le_refl x)⟩
  le_top := fun a => a.2
  bot    := ⟨QProd.zero, pleq_iff_downset.mp (zero_le x)⟩
  bot_le := fun a => zero_le a.val



lemma le_mk_iff {v : QProd} {y : RawProd} : v ≤ mk y ↔ RawProd.pleq_raw (rep v) y := by
  rw [← pleq_iff_le]
  show RawProd.pleq_raw (rep v) (rep (mk y)) ↔ RawProd.pleq_raw (rep v) y
  exact (pleq_raw_normalize_right (rep v) y).symm

/-- `a ⊓ b ≤ c ↔ pleq_raw (rep a ⊓ rep b) (rep c)`:
    lifts raw-level `⊓` to the QProd order. -/
lemma inf_le_iff_pleq {a b c : QProd} : prune a b ≤ c ↔ RawProd.pleq_raw (rep a ⊓ rep b) (rep c) := by
  have prune_eq : prune a b = mk (rep a ⊓ rep b) := by
    conv_lhs => rw [← mk_rep_eq (q := a), ← mk_rep_eq (q := b)]
    exact prune_mk_mk (rep a) (rep b)
  rw [prune_eq, ← pleq_iff_le]
  exact (pleq_raw_normalize_left _ _).symm

/-- Heyting implication in `Downset x`: greatest `c ⊑ x` satisfying `a ⊓ c ⊑ b`. -/
def himp_Downset (x : QProd) (a b : Downset x) : Downset x :=
  ⟨mk (RawProd.himp_raw (rep x) (rep a.1) (rep b.1)),
   pleq_iff_downset.mp (pleq_iff_le.mp (by
     show RawProd.pleq_raw (rep (mk (RawProd.himp_raw (rep x) (rep a.1) (rep b.1)))) (rep x)
     exact (pleq_raw_normalize_left _ _).mp (himp_raw_pleq_bound (rep x) (rep a.1) (rep b.1))))⟩

instance (x : QProd) : HeytingAlgebra (Downset x) :=
  HeytingAlgebra.ofHImp (himp_Downset x) (fun a b c => by
    constructor
    · intro h
      exact inf_le_iff_pleq.mpr ((himp_raw_adjunction (pleq_iff_le.mpr a.2)).mp (le_mk_iff.mp h))
    · intro h
      exact le_mk_iff.mpr ((himp_raw_adjunction (pleq_iff_le.mpr a.2)).mpr (inf_le_iff_pleq.mp h)))

end QProd
