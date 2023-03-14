/-
Copyright (c) 2023 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author : Kevin Buzzard
-/

import tactic
import combinatorics.simple_graph.connectivity -- paths, cycles etc in graph theory

/-

Cut and pasted directly from the module docstring from the file imported above:

# Graph connectivity

In a simple graph,

* A *walk* is a finite sequence of adjacent vertices, and can be
  thought of equally well as a sequence of directed edges.

* A *trail* is a walk whose edges each appear no more than once.

* A *path* is a trail whose vertices appear no more than once.

* A *cycle* is a nonempty trail whose first and last vertices are the
  same and whose vertices except for the first appear no more than once.

(and then there's a warning that in topology some of these words are
used to mean different things)

So of course the question is how to actually do this in Lean. Here's how.
Let `G` be a simple graph with vertex set `V`, and say `v,w,x` in `V`

-/

variables (V : Type) (G : simple_graph V) (v w x : V)

-- The type of all walks from `v` to `w`

example : Type := G.walk v w

-- The empty walk from `v` to `v`

example : G.walk v v := simple_graph.walk.nil' v

-- oh that's a bit annoying, let's open `simple_graph`

open simple_graph

example : G.walk v v := walk.nil' v

-- Add an edge to the beginning of a walk

example (h : G.adj v w) (a : G.walk w x) : G.walk v x := walk.cons' v w x h a 

-- There's also walk.cons where you don't have to specify the vertices

example (h : G.adj v w) (a : G.walk w x) : G.walk v x := walk.cons h a 

-- concatenation of walks

example (a : G.walk v w) (b : G.walk w x) : G.walk v x := a.append b

-- Let `a` be a walk from `v` to `w`

variable (a : G.walk v w)

-- length of `a` is a natural

example : ℕ := a.length

-- reverse of `a`

example : G.walk w v := a.reverse

-- n'th vertex visited in `a`

example (n : ℕ) : V := a.get_vert n

-- 0'th vertex is where we start

example : a.get_vert 0 = v := walk.get_vert_zero a

-- (Walk length)'th vertex is where we end.

example : a.get_vert a.length = w := walk.get_vert_length a

-- Support of `a` is the list of vertices it goes through

example : list V := a.support

-- Edges of `a` is the list of edges it goes through

example : list (sym2 V) := a.edges

-- A walk is a *trail* if it has no repeating edges.

example : Prop := a.is_trail

-- A walk is a *path* if it has no repeating vertices.

example : Prop :=  a.is_path

-- Paths are sufficiently common that `G.path v w` is defined to be the
-- subtype `{p : G.walk v w // p.is_path}`. So to give a term of type `G.path v w`
-- is to give a pair consisting of a walk `p : G.walk v w` and a proof of `p.is_path`.

-- A walk is a *circuit* at `v : V` if it's a nonempty trail beginning and ending at `v`.

example (b : G.walk v v) : Prop := b.is_circuit

-- A walk is a *cycle* at `v : V` if it's a circuit at `v` whose only repeating vertex
-- is `v` (which appears exactly twice).

example (b : G.walk v v) : Prop := b.is_cycle

-- Exercise : give an example of a circuit which isn't a cycle. Can you do it in Lean?
@[reducible] def G5 : simple_graph (fin 5) := complete_graph _
lemma e10 : G5.adj 1 0 := dec_trivial
lemma e21 : G5.adj 2 1 := dec_trivial
lemma e02 : G5.adj 0 2 := dec_trivial
lemma e30 : G5.adj 3 0 := dec_trivial
lemma e43 : G5.adj 4 3 := dec_trivial
lemma e04 : G5.adj 0 4 := dec_trivial
 
def a5 : G5.walk 0 0 := 
((((((walk.nil' 0).cons e10).cons e21).cons e02).cons e30).cons e43).cons e04

example : a5.is_circuit :=
{ edges_nodup := dec_trivial,
  ne_nil := by rintro ⟨⟩, }

example : ¬ a5.is_cycle :=
begin
  rintro ⟨-, h⟩,
  revert h,
  refine @list.duplicate.not_nodup _ _ 0 _,
  simp [a5],
  dec_trivial,
end

-- Example theorem in the API: given a walk `p` from `v` to `u` and an edge from `u` to `v`,
-- putting them together gives a cycle iff `p` is a path and the edge from `u` to `v`
-- is not in the edges of `p`.

example {u v : V} (p : G.walk v u) (h : G.adj u v) :
  (walk.cons h p).is_cycle ↔ p.is_path ∧ ¬ ⟦(u, v)⟧ ∈ p.edges :=
walk.cons_is_cycle_iff p h

-- Given a walk from `v` to `w` and a vertex `u` in the support of the walk,
-- truncate the walk so it starts at `v` and finishes at `u`.

open_locale classical
noncomputable theory -- don't ask me

example (a : G.walk v w) (u : V) (hu : u ∈ a.support) : G.walk v u :=
a.take_until u hu

-- With the same hypotheses, return the rest of the walk from `u` to `w`
example (a : G.walk v w) (u : V) (hu : u ∈ a.support) : G.walk u w :=
a.drop_until u hu

-- Example in the API : those two walks added together give the original
-- walk again

example (a : G.walk v w) (u : V) (hu : u ∈ a.support) :
(a.take_until u hu).append (a.drop_until u hu) = a := walk.take_spec a hu

-- Two vertices `u` and `v` satisfy `G.reachable u v : Prop` if there's a walk from `u` to `v`.
example : G.reachable v w ↔ nonempty (G.walk v w) := iff.rfl -- true by definition

-- Can you show that `G.reachable` is an equivalence relation?
example : equivalence (G.reachable) :=
begin
  refine ⟨_, _, _⟩,
  { intro a,
    exact ⟨walk.nil' a⟩, },
  { rintro v w ⟨a⟩,
    exact ⟨a.reverse⟩, },
  { rintro v w x ⟨a⟩ ⟨b⟩,
    exact ⟨a.append b⟩, }, 
end

-- A graph is "preconnected" if `G.reachable v w` is true for any `v w : V`.
-- Note that this includes the empty graph with `V` empty, for silly logic reasons.

example : G.preconnected ↔ ∀ v w : V, G.reachable v w := iff.rfl -- true by definition

-- A graph is connected iff it's preconnected and nonempty.

example : G.connected ↔ G.preconnected ∧ nonempty V :=
begin
  exact connected_iff G,
end

