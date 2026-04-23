import Prod.shallow
import Prod.heyting
import Mathlib.Order.BooleanAlgebra.Defs
import Mathlib.Data.Finset.BooleanAlgebra

namespace RawProd

private def compl_list : List RawProd → List RawProd → List RawProd
  | [],       _        => []
  | x :: xs,  []       => x :: compl_list xs []
  | x :: xs,  y :: ys  => (if y = zero then x else zero) :: compl_list xs ys

@[simp]
lemma compl_list_nil {xs : List RawProd} : compl_list xs [] = xs := by
  induction xs with
  | nil => rw [compl_list]
  | cons xh xt ih => rw [compl_list, List.cons.injEq]; exact ⟨rfl, ih⟩


lemma brak_compl_list_pleq (xs ys : List RawProd) : brak (compl_list xs ys) ⊑ brak xs := by
  induction xs generalizing ys with
  | nil => rw [compl_list]; exact pleq_raw_refl
  | cons xh xt ih =>
    cases ys with
    | nil => rw [compl_list_nil]; exact pleq_raw_refl
    | cons yh yt =>
      simp only [compl_list, cons_pleq_cons_iff]
      constructor
      · cases yh
        · simp only [ite_true]; exact pleq_raw_refl
        · simp only [brak_neq_zero, ite_false]; exact zero_pleq
      · apply ih

lemma prune_compl_list_allzero (xs ys : List RawProd) :
    allzero (prune_list ys (compl_list xs ys)) := by
  induction ys generalizing xs with
  | nil => simp only [allzero, prune_list, List.length_nil, List.replicate_zero]
  | cons yh yt ih =>
    cases xs with
    | nil => simp only [allzero, compl_list, prune_list_nil_right, List.length_nil, List.replicate_zero]
    | cons xh xt =>
      change allzero (prune_raw yh (if yh = zero then xh else zero) :: prune_list yt (compl_list xt yt))
      rw [allzero, List.length_cons, List.replicate_succ, List.cons.injEq]
      refine ⟨?_, ih xt⟩
      split_ifs with h
      · simp only [h, zero_prune_eq_zero]
      · simp only [prune_zero_eq_zero]

lemma graft_compl_list_equiv_xs {xs ys : List RawProd} (hs : shallow xs)
    (hle : brak ys ⊑ brak xs) :
    (brak (graft_list ys (compl_list xs ys))).equiv (brak xs) := by
  induction ys generalizing xs with
  | nil => simp only [compl_list_nil, graft_list_nil_left, equiv_refl]
  | cons yh yt ih =>
    cases xs with
    | nil =>
      simp only [compl_list, graft_list_nil_right]
      exact brak_equiv_nil_iff_allzero.mpr (brak_pleq_nil_iff_allzero.mp hle)
    | cons xh xt =>
      simp only [compl_list, graft_list]
      obtain ⟨_, hs2⟩ := shallow_cons_iff.mp hs
      obtain ⟨hh, ht⟩ := cons_pleq_cons_iff.mp hle
      refine cons_equiv_cons_iff.mp ⟨?_, ih hs2 ht⟩
      split_ifs with h
      · simp only [equiv_refl, h, equiv_zero_eq_zero, zero_graft_eq_self]
      · rw [graft_zero_eq_self]
        have hxh_nil : xh ⊑ nil := by
          have := shallow_iff_pleq_nil.mp hs 0; rwa [get_cons_zero] at this
        exact equiv_trans (pleq_nil_equiv_nil (pleq_transitivity hh hxh_nil) h)
                          (pleq_nil_equiv_nil hxh_nil (fun heq => h (pleq_zero_eq_zero (heq ▸ hh)))).symm



end RawProd

namespace QProd

open RawProd

-- ---------------------------------------------------------------------------
-- NonZeroDownset and its canonical Lattice
-- ---------------------------------------------------------------------------

def NonZeroDownset (x : QProd) := {y : QProd // nil ≤ y ∧ y ≤ x}

-- `@[reducible]` keeps `le a b := a.val ≤ b.val` transparent so the BA instance
-- below unfolds `≤` correctly without a diamond against a second LE instance.
@[reducible] instance (x : QProd) : Lattice (NonZeroDownset x) where
  le a b               := a.val ≤ b.val
  le_refl a            := le_refl a.val
  le_trans _ _ _ h1 h2 := le_trans h1 h2
  le_antisymm _ _ h1 h2 := Subtype.ext (le_antisymm h1 h2)
  inf a b              := ⟨QProd.prune a.val b.val, ⟨le_inf a.2.1 b.2.1, inf_le_left.trans a.2.2⟩⟩
  sup a b              := ⟨QProd.graft a.val b.val, ⟨le_trans a.2.1 le_sup_left, sup_le a.2.2 b.2.2⟩⟩
  inf_le_left a b      := @inf_le_left QProd _ a.val b.val
  inf_le_right a b     := @inf_le_right QProd _ a.val b.val
  le_inf a b c h1 h2   := @le_inf QProd _ a.val b.val c.val h1 h2
  le_sup_left a b      := @le_sup_left QProd _ a.val b.val
  le_sup_right a b     := @le_sup_right QProd _ a.val b.val
  sup_le a b c h1 h2   := @sup_le QProd _ a.val b.val c.val h1 h2

@[simp] lemma nzd_coe_inf (x : QProd) (a b : NonZeroDownset x) :
    (a ⊓ b).val = QProd.prune a.val b.val := rfl

@[simp] lemma nzd_coe_sup (x : QProd) (a b : NonZeroDownset x) :
    (a ⊔ b).val = QProd.graft a.val b.val := rfl

@[reducible] private def nzd_distribLattice (x : QProd) : DistribLattice (NonZeroDownset x) :=
  DistribLattice.ofInfSupLe fun a b c => by
    apply le_of_eq; apply Subtype.ext
    simp only [nzd_coe_inf, nzd_coe_sup]
    exact QProd.distrib a.val b.val c.val

-- ---------------------------------------------------------------------------
-- Auxiliary facts
-- ---------------------------------------------------------------------------

lemma shallow_nil_le {x : QProd} (hx : shallow x) : nil ≤ x := by
  obtain ⟨xs, hxrep, _⟩ := shallow_exists_brak_rep hx
  rw [eq_mk_brak_of_rep hxrep]; exact le_of_mk_pleq nil_pleq_brak

lemma nzd_rep_ne_zero (x : QProd) (a : NonZeroDownset x) : a.val.rep ≠ RawProd.zero := by
  intro h
  have hle : (nil : QProd) ⊑ a.val := pleq_iff_le.mpr a.2.1
  rw [← mk_rep_eq (q := a.val), h] at hle
  exact absurd (mk_pleq_mk_iff.mp hle) (by simp only [pleq_raw, not_false_eq_true])

/-- The representative of an element of `NonZeroDownset x` is a `brak`. -/
lemma nzd_exists_brak_rep {x : QProd} (a : NonZeroDownset x) :
    ∃ ys, a.val.rep = brak ys := by
  rcases ha : a.val.rep with _ | ys
  · exact absurd ha (nzd_rep_ne_zero x a)
  · exact ⟨ys, rfl⟩

private lemma pleq_of_rep_le {xs ys : List RawProd} {a x : QProd}
    (ha : a.rep = brak ys) (hx : x.rep = brak xs) (h : a ≤ x) : brak ys ⊑ brak xs := by
  have h' := pleq_iff_le.mpr h
  rwa [eq_mk_brak_of_rep ha, eq_mk_brak_of_rep hx, mk_pleq_mk_iff] at h'

-- ---------------------------------------------------------------------------
-- BoundedOrder and complement
-- ---------------------------------------------------------------------------

private instance nzd_boundedOrder (x : QProd) (hx : shallow x) : BoundedOrder (NonZeroDownset x) where
  top    := ⟨x, ⟨shallow_nil_le hx, le_refl x⟩⟩
  le_top := fun a => a.2.2
  bot    := ⟨nil, ⟨le_refl nil, shallow_nil_le hx⟩⟩
  bot_le := fun a => a.2.1

private def compl_fn (x : QProd) (a : NonZeroDownset x) : QProd :=
  mk (brak (compl_list
    (match x.rep with | RawProd.brak xs => xs | RawProd.zero => [])
    (match a.val.rep with | RawProd.brak ys => ys | RawProd.zero => [])))

private lemma compl_fn_eq {x : QProd} (xs : List RawProd) (hxrep : x.rep = brak xs)
    (a : NonZeroDownset x) (ys : List RawProd) (harep : a.val.rep = brak ys) :
    compl_fn x a = mk (brak (compl_list xs ys)) := by
  simp only [compl_fn, hxrep, harep]

private instance nzd_compl (x : QProd) (hx : shallow x) : Compl (NonZeroDownset x) :=
  ⟨fun a => ⟨compl_fn x a, by
    obtain ⟨xs, hxrep, _⟩ := shallow_exists_brak_rep hx
    obtain ⟨ys, harep⟩    := nzd_exists_brak_rep a
    rw [compl_fn_eq xs hxrep a ys harep, eq_mk_brak_of_rep hxrep]
    exact ⟨le_of_mk_pleq nil_pleq_brak, le_of_mk_pleq (brak_compl_list_pleq xs ys)⟩⟩⟩

-- ---------------------------------------------------------------------------
-- Forward direction: BooleanAlgebra from shallow
-- ---------------------------------------------------------------------------

instance (x : QProd) (hx : shallow x) : BooleanAlgebra (NonZeroDownset x) := by
  letI := nzd_distribLattice x
  letI := nzd_boundedOrder x hx
  letI := nzd_compl x hx
  exact {
    inf_compl_le_bot := fun a => le_of_eq <| by
      obtain ⟨xs, hxrep, _⟩ := shallow_exists_brak_rep hx
      obtain ⟨ys, harep⟩    := nzd_exists_brak_rep a
      apply Subtype.ext; simp only [nzd_coe_inf]
      rw [show aᶜ.val = mk (brak (compl_list xs ys)) from compl_fn_eq xs hxrep a ys harep,
          eq_mk_brak_of_rep harep]
      show QProd.prune (mk (brak ys)) (mk (brak (compl_list xs ys))) = nil
      exact Quotient.sound (brak_equiv_nil_iff_allzero.mpr (prune_compl_list_allzero xs ys))
    top_le_sup_compl := fun a => le_of_eq <| Eq.symm <| by
      obtain ⟨xs, hxrep, hs⟩ := shallow_exists_brak_rep hx
      obtain ⟨ys, harep⟩    := nzd_exists_brak_rep a
      apply Subtype.ext; simp only [nzd_coe_sup]
      have hle : brak ys ⊑ brak xs := pleq_of_rep_le harep hxrep a.2.2
      rw [show aᶜ.val = mk (brak (compl_list xs ys)) from compl_fn_eq xs hxrep a ys harep,
          eq_mk_brak_of_rep harep]
      show QProd.graft (mk (brak ys)) (mk (brak (compl_list xs ys))) = x
      rw [eq_mk_brak_of_rep hxrep]
      exact Quotient.sound (graft_compl_list_equiv_xs hs hle)
    le_top   := fun a => a.2.2
    bot_le   := fun a => a.2.1
    sdiff_eq := fun _ _ => rfl
    himp_eq  := fun _ _ => rfl }

-- ---------------------------------------------------------------------------
-- Backward direction: BooleanAlgebra on NonZeroDownset x implies x is shallow
-- ---------------------------------------------------------------------------

def singleton_j (j : ℕ) : QProd :=
  mk (brak (List.replicate j RawProd.zero ++ [RawProd.nil]))

lemma singleton_j_mem_NZD_iff {x : QProd} {xs : List RawProd} (hxrep : x.rep = brak xs) (j : ℕ) :
    singleton_j j ∈ {y : QProd | nil ≤ y ∧ y ≤ x} ↔ get xs j ≠ RawProd.zero := by
  have hxeq  := eq_mk_brak_of_rep hxrep
  refine ⟨fun ⟨_, hhi⟩ => ?_, fun hne => ⟨le_of_mk_pleq nil_pleq_brak, ?_⟩⟩
  · rw [singleton_j, hxeq, ← pleq_iff_le, mk_pleq_mk_iff] at hhi
    exact (replicate_nil_pleq_iff xs j).mp hhi
  · rw [← pleq_iff_le, singleton_j, hxeq, mk_pleq_mk_iff]
    exact (replicate_nil_pleq_iff xs j).mpr hne

/-- Backward direction: if `NonZeroDownset x` carries a Boolean-algebra structure
(supplied here as explicit data — `top`, `bot`, `compl` with the two BA axioms), then
`x` is shallow.

The data is taken explicitly rather than as a `[BooleanAlgebra _]` hypothesis to avoid
an instance diamond against the canonical `Lattice (NonZeroDownset x)`. -/
theorem shallow_of_nzd_complemented (x : QProd)
    (top bot : NonZeroDownset x)
    (htop : ∀ a, a ≤ top)
    (hbot : ∀ a, bot ≤ a)
    (compl : NonZeroDownset x → NonZeroDownset x)
    (h_inf : ∀ a, a ⊓ compl a = bot)
    (h_sup : ∀ a, a ⊔ compl a = top) : shallow x := by
  have hnil_le_x : (nil : QProd) ≤ x := le_trans bot.2.1 bot.2.2
  obtain ⟨xs, hxrep⟩ := exists_brak_rep_of_nil_le hnil_le_x
  have hbot_nil : bot.val = nil :=
    le_antisymm (hbot ⟨nil, le_refl nil, hnil_le_x⟩) bot.2.1
  have htop_x : top.val = x :=
    le_antisymm top.2.2 (htop ⟨x, hnil_le_x, le_refl x⟩)
  simp only [QProd.shallow, hxrep]; rw [shallow_iff_pleq_nil]
  intro i
  by_cases hi : get xs i = RawProd.zero
  · rw [hi]; exact zero_pleq
  let e : NonZeroDownset x := ⟨singleton_j i, (singleton_j_mem_NZD_iff hxrep i).mpr hi⟩
  obtain ⟨cs, hcrep⟩ := nzd_exists_brak_rep (compl e)
  have hev : e.val = mk (brak (List.replicate i RawProd.zero ++ [RawProd.nil])) := rfl
  have hcv : (compl e).val = mk (brak cs) := eq_mk_brak_of_rep hcrep
  have hprune_nil : allzero (prune_list (List.replicate i RawProd.zero ++ [RawProd.nil]) cs) := by
    have hval : QProd.prune e.val (compl e).val = nil := by
      rw [← nzd_coe_inf, h_inf]; exact hbot_nil
    rw [hev, hcv, prune_mk_mk] at hval; simp only [prune_raw] at hval
    exact brak_equiv_nil_iff_allzero.mp (Quotient.exact hval)
  have hci_zero : get cs i = RawProd.zero := by
    have h1 := allzero_get_zero hprune_nil i
    rw [get_prune_list, get_replicate_nil_pos] at h1
    exact nil_prune_eq_zero_iff.mp h1
  have hget_equiv : (get xs i).equiv RawProd.nil := by
    have hgraft : QProd.graft e.val (compl e).val = x := by
      rw [← nzd_coe_sup, h_sup]; exact htop_x
    rw [hev, hcv, graft_mk_mk, eq_mk_brak_of_rep hxrep] at hgraft; simp only [graft_raw] at hgraft
    have heq := brak_equiv_get_equiv (Quotient.exact hgraft) i
    rw [get_graft_list, get_replicate_nil_pos, hci_zero, graft_zero_eq_self] at heq
    exact heq.symm
  cases hget : get xs i with
  | zero    => exact zero_pleq
  | brak ys =>
    rw [hget] at hget_equiv
    exact brak_pleq_nil_iff_allzero.mpr (brak_equiv_nil_iff_allzero.mp hget_equiv)

end QProd
