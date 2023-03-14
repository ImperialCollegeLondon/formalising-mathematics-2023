/-
Copyright (c) 2023 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author : Kevin Buzzard
-/

import tactic
import combinatorics.simple_graph.acyclic -- trees and forests
/-

# Trees and forests

A *forest* is a graph with no cycles. A *tree* is a connected forest.

Here's how to do this in Lean. Let `G` be a graph with vertex set `V`.

-/

variables (V : Type) (G : simple_graph V)

-- Here's how to say "G is a forest"

example : Prop := G.is_acyclic

-- It's defined to mean "For all `v : V`, every walk from `v` to `v` is not a cycle. "

example : G.is_acyclic ↔ ∀ (v : V) (p : G.walk v v), ¬ p.is_cycle :=  
begin
  refl,
end

-- Here's how to say "G is a tree"

example : Prop := G.is_tree

example : G.is_tree ↔ G.connected ∧ G.is_acyclic:=
begin
  exact G.is_tree_iff,
end

-- Here are some harder theorems from the library. Recall that a *path* is a walk
-- with no repeated vertices.

-- A graph is acyclic iff for all `v w : V`, there's at most one path from `v` to `w`.
example : G.is_acyclic ↔ ∀ (v w : V) (p q : G.path v w), p = q :=
simple_graph.is_acyclic_iff_path_unique

-- A graph is a tree iff `V` is nonempty and for all `v w : V`, 
-- there's exactly one path from `v` to `w`.
example : G.is_tree ↔ nonempty V ∧ ∀ v w : V, ∃! (p : G.walk v w), p.is_path :=
simple_graph.is_tree_iff_exists_unique_path

-- If you want a logic puzzle, rephrase this in terms of `G.path`
example : G.is_tree ↔ nonempty V ∧ ∀ v w : V, ∃! (p : G.path v w), true :=
begin
  rw simple_graph.is_tree_iff_exists_unique_path,
  apply and_congr iff.rfl,
  apply forall_congr, intro v,
  apply forall_congr, intro w,
  split,
  { rintro ⟨p,hp,hp2⟩,
    refine ⟨⟨p, hp⟩, true.intro, _⟩,
    rintro ⟨q, hq⟩ -,
    ext,
    exact hp2 _ hq, },
  { rintro ⟨⟨p, hp⟩, -, h2⟩,
    refine ⟨p, hp, λ q hq, _⟩,
    specialize h2 ⟨q, hq⟩ true.intro,
    cases h2,
    refl, },
end

-- If you want a hard graph theory puzzle, prove that in a finite tree, 
-- 1 + the number of edges equals the number of vertices.
-- I don't think this is in the library and it would be a neat project.

open_locale classical

example (V : Type) [fintype V] (G : simple_graph V) (hG : G.is_tree) :
  1 + finset.card (G.edge_finset) = fintype.card V :=
sorry

