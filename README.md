# prod_proofs

This repo contains the proofs of the major results of productive numbers. The proofs are mostly straightforward, but translating them into lean has been a massive headache - in particular nested induction over lists of lists. If you're able to fix these lean proofs, would be much appreciated :)


## Definitions

Definition of a productive number. This is written up (albeit messily) in defs.lean.

``inductive prod_num : Type

| p0 : prod_num

| pli : List prod_num → prod_num

deriving Repr``

By definition, padding zeros does not change a prod, so $[x, y] = [x, y, p0]$ and so on.

Interpretation:
* $eval(p0) = 0$
* $eval([x_1, x_2, ..., x_n]) = 2^{eval(x_1)} \times 3^{eval(x_2)} \times ... \times p_n^{eval(x_n)}$ (where $p_n$ is the nth prime)

Inequality:
1. $\forall x, 0 \leq x$
2. $x_1 \leq y_1, ..., x_n \leq y_n \implies [x_1, ..., x_n] \leq [y_1, ..., y_n]$ (can assume same length by padding)

Prune:
* $0 \land x = 0 = x \land 0$
* $[x_1, ..., x_n] \land [y_1, ..., y_n] = [x_1 \land y_1, ..., x_n \land y_n]$

Graft:
* $0 \lor x = x = x \lor 0$
* $[x_1, ..., x_n] \lor [y_1, ..., y_n] = [x_1 \lor y_1, ..., x_n \lor y_n]$


## Proofs

### Isomorphism

Every natural number has a unique productive representation (up to padding). Various parts of this proof have all failed miserably in nat_iso.lean

(existence is clear)

Uniqueness (strong induction):
* Base cases for $0$ and $1 = [] = [0] = ...$ are immediate
* IH: every $2 \leq m < n$ has productive unique representation.
* By unique factorisation, $n$ uniquely factorises as $2^{e_1} \times 3^{e_2} \times ... \times p_k^{e_k}$
* Since every $e_i < n$, by IH each $e_i$ has unique productive representation $p(e_i)$
* So $[p(e_1), p(e_2), ..., p(e_k)]$ is the unique productive representation of $n$.


### Poset

$\leq$ is a partial order. Proofs are straightforward, but lean translations tricky (see poset.lean)

Reflexivity:
* $0 \leq 0$ by (1)
* Suppose $x_1 \leq x_1, ..., x_n \leq x_n$. Then $[x_1, ..., x_n] \leq [x_1, ..., x_n]$ by (2).

Anti-symmetry ($x \leq y \implies y \leq x \implies x = y$):
* ($x=0$) If $y \leq 0$ means $y = 0$ by (1). 
* ($y=0$) same as above
* ($x = [x_1, ...,x_n], y = [y_1, ..., y_n]$). IH: $x_i \leq y_i \implies y_i \leq x_i \implies x_i = y_i$. 
    - $x \leq y$ implies $x_i \leq y_i$ by (2).
    -  Similary, $y \leq x$ implies $y_i \leq x_i$
    - By IH, $x_i = y_i$. Therefore, $[x_1, ..., x_n] = [y_1, ..., y_n]$, so $x = y$.


Transitivity ($x \leq y \leq z \implies x \leq z$):
* ($x = 0$) $0 \leq z$ by (1)
* ($y = 0$) $x \leq 0$ implies $x = 0 \leq z$ by (1)
* ($z = 0$) $y \leq 0$ implies $y = 0$ which implies $x = 0 \leq z$ as above
* ($x = [x_1, ..., x_n], y=[y_1, ..., y_n], z = [z_1, ..., z_n]$). IH: $x_i \leq y_i \leq z_i \implies x_i \leq z_i$
    - $x \leq y$ implies $x_i \leq y_i$ by (2)
    - $y \leq z$ implies $y_i \leq z_i$ by (2)
    - $x_i \leq z_i$ by IH
    - $x = [x_1, ..., x_n] \leq [z_1, ..., z_n] = z$ by (2)

### Lattice

graft ($\lor$) and prune ($\land$) induce a distributive lattice. Restricting to sublattices (i.e. $\{x : 0 \leq x \leq n\}$), gives a Heyting algebra. If $n$ is square-free (and $\bot = []$), its a Boolean algebra. Lean proofs not even attempted yet.

The partial order of a lattice is usually defined as $a \leq b \iff a \land b = a$. This coincides with the definition of inequality above since:
* $0 \land b = 0$. Thus $0 \leq x, \forall x$.
* Suppose $a_i \leq b_i$. Then $a_i \land b_i = a_i$. Thus $a \land b = [a_1 \land b_1, ..., a_n \land b_n] =_{(IH)} = [a_1, ..., a_n] = a$
Other direction similar.


Idempotence:
* $a \lor a = a$
    - ($a=0$) $0 \lor 0 = 0$
    - ($a = [a_1, ..., a_n]$). IH: $a_i \lor a_i = a_i$.
        - $a \lor a = [a_1 \lor a_1, ..., a_n \lor a_n]$. By IH, this is $[a_1, ..., a_n] = a$
* $a \land a = a$ (effectively identical to above)

Commutativity: dull


Associativity: exceedingly dull


Aborption:
* $a \lor (a \land b) = a$
    - ($a=0$). $0 \land b = 0$ and $0 \lor 0 = 0$.
    - ($b=0$). $a \land 0 = 0$ and $a \lor a = a$ (by idempontence).
    - ($a=[a_1, ..., a_n], b=[b_1, ..., b_n]$). IH: $a_i \lor (a_i \land b_i) = a_i$. 
        - Then $a \lor (a \land b) = a \lor [a_1 \land b_1, ..., a_n \land b_n] = [a_1 \lor (a_1 \land b_1), ..., a_n \lor (a_n \land b_n)] =_{(IH)} [a_1, ..., a_n] = a$
* $a \land (a \lor b) = a$
    - ($a=0$). $0 \land (0 \lor b) = 0 \land b = 0$
    - ($b=0$). $a \lor 0 = a$ and $a \land a = a$ (by idempotence)
    - ($a=[a_1, ..., a_n], b=[b_1, ..., b_n]$). As with other absorption rule

Distributivity ($a \land (b \lor c) = (a \land b) \lor (a \land c)$ ):
* ($a=0$) $0 \land (b \lor c) = 0 = 0 \lor 0 = (0 \land b) \lor (0 \land c)$
* ($b=0$) $a \land (0 \lor c) = a \land c = 0 \lor (a \land c) = (a \land 0) \lor (a \land c)$
* ($c=0$) same as $b=0$ case
* $a = [a_1, ..., a_n], b = [b_1, ..., b_n], c = [c_1, ..., c_n]$. IH: $a_i \land (b_i \lor c_i) = (a_i \land b_i) \lor (a_i \land c_i)$
    - $a \land (b \lor c) = a \land [b_1 \lor c_1, ..., b_n \lor c_n] = [a_1 \land (b_1 \lor c_1), ..., a_n \land (b_n \lor c_n)]$
   
   $=_{(IH)} [(a_1 \land b_1) \lor (a_1 \land c_1), ..., (a_n \land b_n) \lor (a_n \land c_n)] = (a \land b) \lor (a \land c)$




Heyting (for every $a, b$ there is a greatest $x$ s.t. $a \land x \leq b$)
* ($a = 0$). Since $0 \land x = 0$, for any $x$, we can pick the largest $x = \top$. 
* ($b = 0$). If $a \land x \leq 0$, then $a \land x = 0$. Since $a$ is arbitrary, $x$ must be $0$.
* ($a = [a_1, ..., a_n], b = [b_1, ..., b_n]$) IH: $x_i$ is the greatest such that $a_i \land x_i \leq b_i$. 
    - Since $a_i \land x_i \leq b_i$, $[a_1 \land x_1, ..., a_n \land x_n] \leq b$. Thus we can choose $x = [x_1, ..., x_n]$.
    - Now suppose for contradiction there were some $y > x$ such that $a \land y \leq b$. Then $[y_1, ..., y_n] > [x_1, ..., x_n]$, so there is some $j$ such that $y_j > x_j$. But then $a_j \land y_j \leq b_j$, which contradicts the IH.  




Boolean (every $a$ has a complement $\neq a$ such that $a \lor \neg a = \top, a \land \neg a = []$)
* This only works for sublattices of depth at most 2 (productive equivalent of square-free)
* Since $\top$ is square-free, it is just a list of $0$ and $[]$. So the complement of $a$ is just swapping $0$ and $[]$ in all the positions which are $[]$ in $\top$ originally (to maintain closure).
 - eg in the sublattice of 30 ($[[], [], []]$), the complement of $[[], 0, []]$ is $[0, [], 0]$.