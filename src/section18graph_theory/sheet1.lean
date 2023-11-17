/-
Copyright (c) 2023 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author : Kevin Buzzard
-/

import tactic
import combinatorics.simple_graph.basic -- definition of graph

namespace section18sheet1
/-

# Graph theory

A year ago Lean's graph theory was a bit patchy, but now I think
it's robust enough to be taken seriously as a topic for a final project.
This sheet is just an overview of the basic API for graphs; there are
no sorrys.

So, how do graphs work in Lean? Actually it took a long time
to come up with a definition people were happy with. One issue
is that different people mean different things by "graph". In this
section we're going to stick to "simple graphs", which means
that you have a type of vertices `V`, and edges go between two
distinct vertices in `V`. The rules for a simple graph:

1) Edges are undirected (so they don't have a source and a target, they
just have two ends, which are vertices)
2) You can't have more than one edge between two distinct vertices.
3) You can't have an edge going from a vertex to itself.

Because of rule 2, you can represent an edge as a yes/no question:
"is there an edge between `v` and `w` or not?". In other words
you can represent edges as a function `adj: V → V → Prop`, and you
don't need a separate set or type `E` for edges. `adj` is short
for "adjacent", so `adj v w` means "there's an edge between `v` and `w`,
i.e. "`v` is adjacent to `w`".

Rule 1 means that `adj` is symmetric (if `v` is adjacent to `w` then
`w` is adjacent to `v`), and rule 3 means that it is irreflexive,
i.e. `∀ v, ¬ adj v v`.

Here's how to say "let `G` be a (simple) graph with vertex set `V`"

-/

variables (V : Type) (G : simple_graph V)

-- Here's how to say two edges are adjacent

example (v w : V) : Prop := G.adj v w

-- If v is adjacent to w then w is adjacent to v
example (v w : V) : G.adj v w → G.adj w v := G.adj_symm

-- v isn't adjacent to itself
example (v : V) : ¬ G.adj v v := G.irrefl

/-

Longish interlude: here's how to make a square graph. It's quite laborious. 
Lean is better at proving theorems than making explicit examples!

v1 -- v2
|     |
|     |
v3 -- v4
-/

section square_graph

-- the vertex set of the square graph; we make it a type with four terms
inductive sqV : Type
| v1 : sqV
| v2 : sqV
| v3 : sqV
| v4 : sqV

open sqV -- so I can write `v1` not `sqV.v1`

-- here's one boring way of making the edges -- an inductive proposition
inductive sqE : sqV → sqV → Prop
| e12 : sqE v1 v2
| e21 : sqE v2 v1
| e24 : sqE v2 v4
| e42 : sqE v4 v2
| e34 : sqE v3 v4
| e43 : sqE v4 v3
| e13 : sqE v1 v3
| e31 : sqE v3 v1

-- Now let's make the graph
def sqG : simple_graph sqV :=
{ adj := sqE,
  symm := begin
    -- do all the cases for the two vertices and the edge
    rintro (_ | _ | _ | _) (_ | _ | _ | _) (_ | _ | _ | _ | _ | _ | _ | _),
    -- now 8 goals; find the right constructor for sqE in all cases
    repeat {constructor}, 
  end,
  loopless := begin
    rintro (_ | _ | _ | _) (_ | _ | _ | _ | _ | _ | _ | _),
  end }

end square_graph

-- Here's how to make a triangle graph; it's rather easier

-- Here `fin 3` is the "canonical" type with 3 terms; to give a term of type `fin 3`
-- is to give a pair consisting of a natural `n` and a proof that `n < 3`.
-- Here the `complete_graph` function is doing all the work for you.
example : simple_graph (fin 3) := complete_graph (fin 3)

-- The collection of all simple graphs on a fixed vertex set `V` form a Boolean algebra
-- (whatever that is)
example : boolean_algebra (simple_graph V) := by apply_instance

-- and in particular they form a lattice, so you can do stuff like this:

example : simple_graph V := ⊥ -- empty graph
example : simple_graph V := ⊤ -- complete graph
example (G H : simple_graph V) : simple_graph V := G ⊔ H -- union of vertices
-- etc etc, and you can even do this
example (G : simple_graph V) : simple_graph V := Gᶜ -- complement, i.e. an edge exists in `Gᶜ` between
                                                    -- distinct vertices `v` and `w` iff it doesn't
                                                    -- exist in `G`

-- The *support* of a graph is the vertices that have an edge coming from them.

example (v : V) : v ∈ G.support ↔ ∃ w, G.adj v w := 
begin
  refl, -- true by definition
end



-- The `neighbor_set` of a vertex is all the vertices connected to it by an edge.

example (v : V) : set V := G.neighbor_set v

example (v w : V) : w ∈ G.neighbor_set v ↔ G.adj v w := iff.rfl -- true by defn

-- The type `sym2 V` is the type of unordered pairs of elements of `V`, i.e. `V × V`
-- modulo the equivalence relation generated by `(v,w)~(w,v)`.
-- So you can regard the edges as a subset of `sym2 V`, and that's `G.edge_set`

example : set (sym2 V) := G.edge_set

-- You can use `v ∈ e` notation if `e : sym2 v`
-- For example, `G.incidence_set v` is the set of edges coming out of `v`,
-- regarded as elements of `sym2 V`

example (v : V) : G.incidence_set v = {e ∈ G.edge_set | v ∈ e} := rfl

-- You can delete a set of edges from `G` using `G.delete_edges`

example (E : set (sym2 V)) : simple_graph V := G.delete_edges E 

-- if E contains edges not in G then this doesn't matter, they're just ignored.

-- You can push a graph forward along an injection

example (W : Type) (f : V ↪ W) : simple_graph W := G.map f 

-- and pull it back along an arbitrary map

example (U : Type) (g : U → V) : simple_graph U := G.comap g 

-- The degree of a vertex is the size of its neighbor_set.
-- Better assume some finiteness conditions to make this work.

variable [G.locally_finite]

-- now we have `finset` versions of some `set` things. For example
example (v : V) : G.degree v = finset.card (G.neighbor_finset v) := rfl 

-- If `H` is another graph on a vertex set `W` 
variables (W : Type) (H : simple_graph W)

-- then we can consider types of various maps between graphs

example : Type := G →g H -- maps f:V → W such that v₁~v₂ -> f(v₁)~f(v₂)
example : Type := G ↪g H -- injections f : V → W such that v₁~v₂ ↔ f(v₁)~f(v₂)
example : Type := G ≃g H -- isomorphisms of graphs

end section18sheet1