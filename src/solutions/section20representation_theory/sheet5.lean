/-
Copyright (c) 2023 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author : Kevin Buzzard
-/

import representation_theory.fdRep -- finite-dimensional representations

/-

Here is a fourth way of doing undergraduate representation theory in Lean ;-)

# Finite dimensional representations via category theory

As well as the category `Rep k G` there's the full subcategory of finite-dimensional
representations `fdRep k G`. Let's see it in action!

-/

variables {k : Type} [field k] {G : Type} [group G] 

/-

The category of representations of G on finite-dimensional k-vector spaces is called `fdRep k G`

-/

example : Type 1 := fdRep k G

/-

Given `V : fdRep k G` here's how to recover the `representation`:

-/

example (V : fdRep k G) : representation k G V := V.ρ -- note: the type is `representation k G ↥V`

/-

Conversely, given a finite-dimensional `representation` we can make an object
of the category.

-/

example (V : Type) [add_comm_group V] [module k V] [finite_dimensional k V] 
  (ρ : representation k G V) : fdRep k G :=
fdRep.of ρ

-- Here's how to say that a finite-dimensional representation is irreducible:

open category_theory

example (V : fdRep k G) : Prop := simple V -- this is `category_theory.simple`

-- Here's Schur's lemma, stated and proved in the `fdRep` language:

open finite_dimensional

open_locale classical

-- if k is alg closed and V,W are irreducible then Hom(V,W) has dimension 1
-- if V ≅ W, and 0 otherwise.
example [is_alg_closed k] (V W : fdRep k G) [simple V] [simple W] : 
  finrank k (V ⟶ W) = if nonempty (V ≅ W) then 1 else 0 :=
fdRep.finrank_hom_simple_simple V W
