/-
Copyright (c) 2023 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author : Kevin Buzzard
-/

import tactic -- imports all the Lean tactics
import linear_algebra.finite_dimensional -- finite-dimensional vector spaces

/-!

# Vector spaces

Ok so groups in Lean are called `group` and fields are called `field`, so
I think I owe you an explanation for why vector spaces are called `module`.

The lie is that `module` is French for vector space, and we used a French source.
If you're happy with that explanation, then you can skip the actual explanation below.

The truth is the following. The definition of a vector space `V` over a field `k` is:

1) `V` is an abelian group
2) If `r : k` and `v : V` there's an element `r • v : V`
3) Axioms for `•`: `(r + s) • v = r • v + s • v`, `r • (v + w) = r • v = r • w`,
  `1 • v = v` and `(r * s) • v = r • (s • v)`.

Recall that `k` was a field. Fields have division and inverses (except for 0), 
but look at those axioms: there is no mention of inverses or division for `k` in the axioms
of a vector space. The only things we use on `k` are `1`, `+` and `*`. 

This means that we can make the *definition* of a vector space just under
the assumption that `k` is a `ring`, rather than a `field`, although of course
fewer things will be true (for example, over a general ring it is not true that
every vector space has a basis). However, when `k` is a ring, mathematicians don't
call these things vector spaces; they call them *modules*. So the way we say
"let `V` be a vector space over `k`" in Lean is "let `V` be a module over `k`".

Note to self: we should be able to add notation `vector_space` for `module` in a locale.
But let's just tell them it's French for vector space.
-/

-- Let `k` be a field and let `V` be a vector space over `k`
variables (k : Type) [field k] (V : Type) [add_comm_group V] [module k V]

-- The field `k` acts on the vector space `V` and the notation for this is `•`, 
-- which is notation for `smul`. We don't use `mul` because for `a * b` to make
-- sense in Lean we need `a` and `b` to have the same type. Here `a : k` and `v : V`
-- so this isn't satisfied.

example (a : k) (v : V) : V := a • v

-- Axioms for a vector space

variables (a b : k) (v w : V)

example : a • (v + w) = a • v + a • w := smul_add a v w
example : (a + b) • v = a • v + b • v := add_smul a b v
example : (1 : k) • v = v := one_smul k v
example : a • (b • v) = (a * b) • v := smul_smul a b v

-- Other standard facts about vector spaces:
example : (a - b) • v = a • v - b • v := sub_smul a b v 
example : (0 : k) • v = 0 := zero_smul k v

/-

## Subspaces

The type of subspaces of a vector space is called `subspace k V`. You
have to mention `k` because there are real world examples like `ℂⁿ` which
are vector spaces over both the reals and the complexes, so they have
more real subspaces than complex subspaces. 

Subspaces of a vector space form a complete lattice, so Lean uses lattice notation for them.

-/

-- let `X` and `Y` be subspaces of `V`
variables (X Y : subspace k V)

-- Note that `X` and `Y` are terms not types.

-- How do we say `X ⊆ Y`?

-- #check X ⊆ Y -- doesn't work! `⊆` only works for terms of type `set V`. 

-- We use *lattice notation* and it works fine.

example : Prop := X ≤ Y -- `X ≤ Y` is a true-false statement

example : subspace k V := X ⊓ Y -- intersection of `X` and `Y`, as a subspace

example : subspace k V := X ⊔ Y -- `X` + `Y`, as a subspace. It's the smallest vector subspace of
                                -- `V` containing `X` and `Y`, so it's the sup of `X` and `Y`
                                -- in the lattice of subspaces.

example : subspace k V := ⊥ -- the 0-dimensional subspace

example : subspace k V := ⊤  -- V considered as a subspace of itself; note that
                             -- we can't use V to represent this subspace because
                             -- V is a type, and a subspace of V is a term

-- For elements of subspaces it's just like sets:

example : Prop := v ∈ X -- the type of `v` is `V`, and the true-false statement is `v ∈ X`

-- Let `W` be another `k`-vector space
variables (W : Type) [add_comm_group W] [module k W]

-- `k`-linear maps from `V` to `W` are terms of type `V →ₗ[k] W`. This is notation
-- for `linear_map (ring_hom.id k) V W`.

-- let `φ : V → W` be a linear map
variable (φ : V →ₗ[k] W)

-- Axioms for a linear map:
example : φ (a • v) = a • φ v := φ.map_smul a v
example : φ (v + w) = φ v + φ w := φ.map_add v w

-- quotients work just like in group theory
example := V ⧸ X

-- The linear map from `V` to `V ⧸ X` is called `submodule.mkq X`

example : V →ₗ[k] V ⧸ X := submodule.mkq X

-- ...which is inconsistent with the group theory quotient conventions, something I only 
-- just spotted when preparing this course sheet.

-- You can take the image and preimage of subspaces along a linear map.

example (X : subspace k V) : subspace k W := X.map φ
example (Y : subspace k W) : subspace k V := Y.comap φ

-- Here's an actual question at long last. If φ : V → W is a linear map,
-- if X is a subspace of V and Y a subspace of W, prove that φ(X) ⊆ Y iff X ⊆ φ⁻¹(Y)
example (X : subspace k V) (Y : subspace k W) : X.map φ ≤ Y ↔ X ≤ Y.comap φ :=
begin
  sorry,
end
