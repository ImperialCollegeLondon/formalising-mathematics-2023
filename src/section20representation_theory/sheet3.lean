/-
Copyright (c) 2023 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author : Kevin Buzzard
-/

import representation_theory.basic
import representation_theory.maschke -- Maschke's theorem

/-

# Representation theory via k[G]-modules

It might have struck you as odd that we have a definition of `representation`
but not a definition of map between representations. One reason for this
is that there's another way of thinking about representations, which is
that they are `k[G]-modules`. Here `k[G]` is the so-called group ring associated
to `k` and `G`; it's a vector space with basis indexed by `G`, and multiplication
given by multiplication on `G` and extended linearly, so (∑ aᵢgᵢ)(∑ bⱼhⱼ) := ∑ᵢⱼ(aᵢbⱼ)(gᵢhⱼ)
for `aᵢ, bⱼ : k` and `gᵢ, hⱼ : G`.

Because the construction works with monoids (note that there's no mention of inverses
in the definition of the group ring), it's called `monoid_algebra` in Lean.

-/

variables (k : Type) [field k] (G : Type) [group G]

example : Type := monoid_algebra k G

noncomputable theory -- Lean moans about various things if you don't switch this on
-- Note that this doesn't matter for mathematicians, this is a computer science thing

example : ring (monoid_algebra k G) := infer_instance

-- Turns out that there's a bijection between modules for the group ring k[G],
-- and representations of G on k-vector spaces. The dictionary works like this.
-- Let ρ be a representation of G on a k-vector space V

variables (V : Type) [add_comm_group V] [module k V] (ρ : representation k G V) 

-- Here's the underlying type of the module.

example : Type := ρ.as_module

-- Note that `ρ.as_module` is definitionally equal to `V`, but it knows about `ρ` because `ρ` is in its name.
-- As a result, this works:

example : module (monoid_algebra k G) ρ.as_module := infer_instance

-- This wouldn't work with `ρ.as_module` replaced by `V`, because type class inference wouldn't
-- be able to find `ρ`

-- The other way: let `M` be a `k[G]`-module

variables (M : Type) [add_comm_group M] [module (monoid_algebra k G) M]

-- Here's the representation

example : representation k G (restrict_scalars k (monoid_algebra k G) M) := representation.of_module k G M

-- What's going on here? The issue is that type class inference can't by default find the k-module
-- structure on `M`, so this `restrict_scalars k (monoid_algebra k G) M` thing means "`M`, but with
-- the `k`-action coming from the monoid_algebra k G action"
-- It's defeq to `M`:

example : restrict_scalars k (monoid_algebra k G) M = M := rfl 

-- So another way of doing morphisms between representations is as `monoid_algebra k G` morphisms.

-- Let σ be another representation
variables (W : Type) [add_comm_group W] [module k W] (σ : representation k G W) 

-- The type of G-morphisms between `ρ` and `σ`

example : Type := ρ.as_module →ₗ[monoid_algebra k G] σ.as_module 

-- If you do it this way, then you don't have to make G-morphisms. 

-- Let φ be a G-morphism

variable (φ : ρ.as_module →ₗ[monoid_algebra k G] σ.as_module)

-- Then you can evaluate it at elements of `V`

example (v : V) : W := φ v 

-- This works because `V = ρ.as_module` definitionally. 

-- The k[G]-module language is how Lean expresses Maschke's theorem.

-- Assume `G` is finite, and its order is invertible in `k`
variables [fintype G] [invertible (fintype.card G : k)]

-- Assume `V` and `W` are k[G]-modules (with the k[G]-action compatible with the k-action)

variables 
  [module (monoid_algebra k G) V] [is_scalar_tower k (monoid_algebra k G) V]
  [module (monoid_algebra k G) W] [is_scalar_tower k (monoid_algebra k G) W]

-- Then every injective k[G]-linear map from `V` to `W` has a one-sided inverse
-- (and hence a complement, namely the kernel of the inverse)

example (φ : V →ₗ[monoid_algebra k G] W) (hφ : φ.ker = ⊥) : 
  ∃ ψ : W →ₗ[monoid_algebra k G] V, ψ.comp φ = linear_map.id :=
monoid_algebra.exists_left_inverse_of_injective φ hφ  