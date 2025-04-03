import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.Nat.Prime.Defs
import Mathlib.Data.Nat.Nth



namespace ProdProofs


-- Define the prod_num type
inductive prod_num : Type
| p0 : prod_num
| pli : List prod_num → prod_num
deriving Repr



/-- Pad a list with n zeros -/
def pad_n (l : List prod_num) (n : Nat) : List prod_num :=
  l ++ List.replicate n prod_num.p0


axiom prod_pad (ps : List prod_num) : prod_num.pli (ps ++ [prod_num.p0]) = prod_num.pli ps

lemma replicate_comm {n : ℕ} : a :: List.replicate n a = List.replicate n a ++ [a] := by
  induction n
  case zero => simp
  case succ d hd =>
    rw [List.replicate_succ]
    simp [List.cons_append]
    assumption

/-- Generalized lemma for padding with any number of zeros -/
@[simp] lemma zeros_append_n {xs : List prod_num} {n : Nat} :
  prod_num.pli xs = prod_num.pli (pad_n xs n) := by
  rw [pad_n]
  induction n
  case zero => simp
  case succ d hd =>
    rw [List.replicate_succ]

    have h1: xs ++ prod_num.p0 :: List.replicate d prod_num.p0 = (xs ++ List.replicate d prod_num.p0) ++ [prod_num.p0] := by
      simp [List.cons_append, replicate_comm]
    rw [h1, hd, prod_pad]



noncomputable def prime_at (n : Nat) : Nat :=
  Nat.nth Nat.Prime n



noncomputable def eval_prod : prod_num → Nat
| .p0 => 0
| .pli l =>
    let rec eval_list (l : List prod_num) (i : Nat) : Nat :=
      match l with
      | [] => 1
      | x :: xs => (prime_at i ^ eval_prod x) * (eval_list xs (i + 1))
      termination_by sizeOf l
    eval_list l 0
termination_by x => sizeOf x
decreasing_by
  simp_wf

lemma eval_empty_1 : eval_prod (prod_num.pli []) = 1 := by
  rw [eval_prod, eval_prod.eval_list]


-- examples
#reduce eval_prod prod_num.p0
#reduce eval_prod (prod_num.pli []) -- 1
#reduce eval_prod (prod_num.pli [prod_num.pli []]) -- 2



noncomputable def prod_factor : Nat → prod_num
  | 0 => prod_num.p0
  | 1 => prod_num.pli []
  | n@(Nat.succ _) =>
      -- Get the list of prime factors and determine the maximum prime factor
      let factor_map := Nat.primeFactorsList n
      let max_prime := factor_map.foldl (fun acc p => max acc p) 2
      let max_index := (factor_map.indexOf max_prime) + 1

      have n_neq_0: n ≠ 0 := by linarith

      prod_num.pli (List.map (λi => prod_factor (n.factorization (prime_at i))) (List.range max_index))

termination_by n => n
decreasing_by
  rename_i n2 h
  simp
  have h2 : n = n2 + 1 := by linarith
  rw [← h2]
  exact Nat.factorization_lt (Nat.nth Nat.Prime i) n_neq_0


def prod_leq : prod_num → prod_num → Prop
| .p0, _ => True
| .pli _, .p0 => False
| .pli xs, .pli ys =>
    match xs, ys with
    | [], _ => True
    | x::xt, [] => prod_leq (.pli xt) (.pli [])
    | x::xt, y::yt => prod_leq x y ∧ prod_leq (.pli xt) (.pli yt)
termination_by px _ => px
decreasing_by
  simp_wf
  simp_wf
  linarith
  simp_wf

def prod_num.as_list : prod_num → List prod_num
| .p0 => [] -- shouldnt ever be called
| .pli xs => xs

def prune : prod_num → prod_num → prod_num
| .p0, _ => .p0
| _, .p0 => .p0
| .pli [], _ => .pli []
| _, .pli [] => .pli []
| .pli (x :: xt), .pli (y :: yt) =>
  .pli (prune x y :: (prune (.pli xt) (.pli yt)).as_list)

-- basically same except base cases
def graft : prod_num → prod_num → prod_num
| .p0, x => x
| x, .p0 => x
| .pli [], x => x
| x, .pli [] => x
| .pli (x :: xt), .pli (y :: yt) =>
  .pli (graft x y :: (graft (.pli xt) (.pli yt)).as_list)


def prod_num.induction {P : prod_num → Prop}
  (hp0 : P p0)
  (hpli : ∀ (ps : List prod_num), (∀ p, p ∈ ps → P p) → P (pli ps))
  (p : prod_num) : P p :=
  match p with
  | p0 => hp0
  | pli ps => hpli ps (fun p h => prod_num.induction hp0 hpli p)

-- Mark it for use with the induction tactic
@[elab_as_elim]
def prod_num.induction_on {P : prod_num → Prop} := @prod_num.induction P


end ProdProofs
