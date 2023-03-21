/-
Copyright (c) 2023 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author : Kevin Buzzard
-/

import representation_theory.basic

/-

# Representation theory

There are two ways to do representation theory -- the way you might guess
(involving vector spaces `(V : Type) [add_comm_group V] [module k V]`) and
a funkier way using category theory. Let's start with the vector space way.

## `representation k G V`

Let `k` be a field (or a commutative ring), let `G` be a group (or a monoid)
and let `V` be a vector space (or module) over `k`. 

Then `representation k G V` is the type of representations of `G` on `V`,
where `G` acts `k`-linearly. It's not a class, because one group `G` can act
in more than one way on a vector space `V`.

-/

-- Let k be a field, G a group and V a k-vector space
variables (k : Type) [field k] (G : Type) [group G] 
  (V : Type) [add_comm_group V] [module k V]

-- Let `ρ` be a representation of `G` on `V`.
variable (ρ : representation k G V)

-- If `g : G` and `v : V` then `ρ(g)v` is done like this:

variables (g : G) (v : V)

example : V := ρ g v

-- Here are the names of some basic lemmas

variables (h : G) (w : V) (c : k)

example : ρ g (v + w) = ρ g v + ρ g w := map_add (ρ g) v w
example : ρ g (c • w) = c • ρ g w := (ρ g).map_smul c w

-- I was quite surprised to find that this doesn't seem to be in the library
example : ρ (g * h) v = ρ g (ρ h v) := 
begin
  rw map_mul,
  rw linear_map.mul_apply,
end

/- Let's talk about this previous proof. `map_mul` is the statement that if `f`
is a group homomorphism then `f(g*h)=f(g)*f(h)`. What is happening is that
the definition of `representation` is this:

`abbreviation representation := G →* (V →ₗ[k] V)`

What's going on here? `V →ₗ[k] V` is the type of `k`-linear maps from `V` to `V`.
This space has a multiplication, given by function composition (composite of two
linear maps is a linear map). This doesn't make it a group! Maps like the zero map
have no inverse (if dim(V)>0). But it does have an identity, namely the 
identity map from `V` to `V`. So it is a monoid, which is a "group without inverses". 
And `G →* (V →ₗ[k] V)` means the `*`-preserving maps from `G` to `V →ₗ[k] V`, or
the monoid homomorphisms if you'd rather, so it's maps `ρ` satisfying `ρ(gh)=ρ(g)*ρ(h)`,
or in other words `ρ(gh)=ρ(g)∘ρ(h)`. If two functions are equal, then they take the
same values everywhere, so we deduce that for all `v`, `ρ(gh)(v)=ρ(g)(ρ(h)v)`, and
that should be what the proof looks like in Lean. 

If `representation` were defined as a `def` then this proof wouldn't work, because
`representation k G V` would be definitionally, but not syntactically, `G →* (V →ₗ[k] V)`,
and the `rw` tactic works up to syntactic equality. One would have to start with
the line `unfold representation` to get `rw map_mul` to work. But because it's
defined as an `abbreviation`, this means that Lean *does* unfold it internally. 
Lean has three kinds of "reducibility settings" for definitions. There is `irreducible`,
which means "never unfold", there is `semireducible`, which is the default, and so
the behaviour that you're used to, and there is `reducible`, which basically means 
"unfold the moment you think it might help". Making a definition with `abbreviation`
makes it `reducible`. So the rewrite works anyway.

Note that the proof of `linear_map.mul_apply` is `refl`, because `f ∘ g` is *defined*
to mean `λ x, f (g x)`, so `(f ∘ g) (x) = f (g x)` is definitionally true. So this
proof works as well:

-/

example : ρ (g * h) v = ρ g (ρ h v) := 
begin
  rw map_mul,
  -- ⊢ `⇑(⇑ρ g * ⇑ρ h) v = ⇑(⇑ρ g) (⇑(⇑ρ h) v)`
  -- and note `ρ g * ρ h` is definitionally `ρ g ∘ ρ h`,
  -- which is definitionally `λ v, (ρ g) (ρ h v)`. So this works:
  refl,
end

-- Let's make a representation! Because internally it's a group homomorphism,
-- which is a structure, we just have to fill in the fields. Let's start with
-- the trivial representation.

example : representation k G V :=
{ to_fun := λ g, 1,
  map_one' := rfl,
  map_mul' := λ g h, by simp }

-- If we have a group homomorphism `χ : G → kˣ` then we can make a representation
-- of `G` on `V` by defining `ρ(g)v=χ(g)•v`. I couldn't find how to construct
-- the "multiply by a scalar" function as a linear map so I had to make the
-- linear map structure explicitly as well.

example (χ : G →* kˣ) : representation k G V :=
sorry

/- If `G` is finite then `G → k` is a vector space with a natural basis indexed by `G`:
   for `g : G` define the function `δᵍ : G → k` sending `g` to `1` and everything else to `0`,
   and then the `δᵍ` are a basis. Now `G` acts naturally on these basis elements
   and hence gives us a representation of `G` on this space. Note that I've done the
   typical mathematician's thing of leaving out some of the details. See if you can
   work them out. -/
  
example : representation k G (G → k) :=
sorry

-- Note that if `G` is infinite, this is not the regular representation on the group ring; 
-- one has to consider finitely supported functions `G →₀ k` instead; this makes things a 
-- bit harder. One of you set up this theory as part of your 2nd project!


