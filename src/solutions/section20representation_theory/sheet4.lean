/-
Copyright (c) 2023 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author : Kevin Buzzard
-/

import representation_theory.Rep -- representation theory via categories

/-

# Representation theory via category theory

It might have struck you as odd that we have a definition of `representation`
but not a definition of map between representations. That's because, for probably
nothing more than coincidental reasons, it was decided to set up representation
theory in Lean directly using categories. So here's how this works.

We start with a field and a group (or a ring and a monoid)
-/

variables {k : Type} [field k] {G : Type} [group G] 

/-

The category of representations of G on k-vector spaces is called `Rep k G`

-/

example : Type 1 := Rep k G

/-

Wooah what is this `Type 1`: that's because the collection of all `k`-vector spaces
is *not a set*: it's too big. In set theory they use the word "class" to indicate
"collection which is too big to be a set"; in Lean we just bump up the universe
level by 1. Turns out that the full name of `Type` is `Type 0`, and if you think
set-theoretically, and think of `X : Type` as a set then you can
think of `X : Type 1` as a class. This universe bumping thing is common in category
theory.

## Category theory in Lean

Let `C` be a category.

-/

open category_theory

variables (C : Type) [category.{0} C] -- the `{0}` means "Hom(X,Y) is a set for all X and Y"!

-- Let `X` and `Y` be objects of `C`

variables (X Y : C)

-- WARNING: the morphisms between `X` and `Y` are not denoted `X → Y` with the usual arrow,
-- you have to use the category theory arrow `\hom` 

example : Type := X ⟶ Y -- not the usual arrow!

example : X ⟶ X := 𝟙 X -- identity morphism

-- Let Z be another object and let φ : X ⟶ Y and ψ : Y ⟶ Z be morphisms
variables (Z : C) (φ : X ⟶ Y) (ψ : Y ⟶ Z)

-- We can compose them

example : X ⟶ Z := φ ≫ ψ -- note the order! If φ and ψ are actual functions, this would be ψ ∘ φ

-- Category axioms:

example : φ ≫ 𝟙 Y = φ := category.comp_id φ
example : 𝟙 X ≫ φ = φ := category.id_comp φ

variables (T : C) (ξ : Z ⟶ T)
example : (φ ≫ ψ) ≫ ξ = φ ≫ (ψ ≫ ξ) := category.assoc φ ψ ξ

/-

There are two notions of "being the same" in category theory; there is isomorphism,
which means what you think it means and is usually far too strong a notion, and there's
a weaker notion called equivalence. This theorem

-/

noncomputable example : Rep k G ≌ Module.{0} (monoid_algebra k G) :=
Rep.equivalence_Module_monoid_algebra

-- says that the category of representations of `G` is equivalent to the category
-- of modules for `monoid_algebra k G`. If you go "full category theory"
-- then this is the dictionary you can use to move between the two points of view.

-- Given an object `V : Rep k G`, the underlying representation of `G` is called `↥V`

example (V : Rep k G) : Type := V -- note the coercion from terms to types, `V` is a term

-- The action of `G` is given by `V.ρ`

example (g : G) (V : Rep k G) (v : V) : V := V.ρ g v

-- Now say `V` and `W` are representations in the sense of category theory

variables (V W : Rep k G)

-- A G-linear map from V to W is a morphism in the category!

variable (α : V ⟶ W) -- this is `\hom` not `→`

-- This α is some abstract morphism. To get the actual map, use α.hom

example (v : V) : W := α.hom v

example (g : G) (v : V) : α.hom (V.ρ g v) = W.ρ g (α.hom v) :=
begin
  -- this was a bit of a kerfuffle!
  have := Action.hom.comm α g,
  have this2 := linear_map.ext_iff.1 this,
  exact this2 v,
end
