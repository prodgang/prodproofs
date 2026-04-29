/-
Copyright (c) 2024 Edwin Agnew. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Edwin Agnew
-/
import ProdNum.RawDefs
import ProdNum.QuotDefs
import ProdNum.Interp
import ProdNum.Bij
import ProdNum.PruneBasic
import ProdNum.GraftBasic
import ProdNum.Poset
import ProdNum.Lattice
import ProdNum.Heyting
import ProdNum.Shallow
import ProdNum.Bool

/-!
# Productive Numbers

This library formalises productive numbers and their main properties.
Every natural number can be represented uniquely as a productive number,
giving a bijection `QProd ≃ ℕ`. The type `QProd` is also a distributive lattice
under graft (`⊔`, pointwise join) and prune (`⊓`, pointwise meet).
-/
