import Prod.quot_defs3

namespace RawProd

def prune_raw : RawProd → RawProd → RawProd
  | zero, _ => zero
  | _, zero => zero
  | cons xs, cons ys => match xs, ys with
    | List.nil, _ => cons List.nil
    | _, List.nil => cons List.nil
    | x::xx, y::yy => cons ((prune_raw x y)::List.map (Function.uncurry prune_raw) (List.zip xx yy))
termination_by n => n
decreasing_by
  simp_wf
  linarith
  sorry



--def graft (x y : QProd) : QProd
def graft_raw : RawProd → RawProd → RawProd
  | zero, y   => y
  | x, zero => x
  | cons xs, cons ys => match xs, ys with
    | List.nil, yy => cons yy
    | xx, List.nil => cons xx
    | x::xx, y::yy => cons ((graft_raw x y)::List.map (Function.uncurry graft_raw) (List.zip xx yy))
termination_by n => n
decreasing_by
  simp_wf
  linarith
  sorry


end RawProd

namespace QProd

def prune : QProd → QProd → QProd :=
  Quotient.lift RawProd.prune_raw


end QProd
