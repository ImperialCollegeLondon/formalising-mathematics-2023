/-
Copyright (c) 2023 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author : Kevin Buzzard
-/

import representation_theory.basic

/-

# Representation theory

Homomorphisms between representations; representations as modules.

-/

-- Let ρ and σ be representations of G on V and W
variables {k : Type} [field k] {G : Type} [group G] 
  {V : Type} [add_comm_group V] [module k V]
  {W : Type} [add_comm_group W] [module k W]
  (ρ : representation k G V) (σ : representation k G W)

-- According to one of my PhD students yesterday, there is no "G-linear map" class!
-- So let's make one.

/-- The G-equivariant linear maps between two representations. -/
@[ext] -- this makes the `ext` tactic work on rep_maps, i.e. it shows that two rep_maps are 
-- the same if they are the same underlying function
structure rep_map (ρ : representation k G V) (σ : representation k G W) : Type :=
(to_linear_map : V →ₗ[k] W)
(map_apply : ∀ (g : G) (v : V), to_linear_map (ρ g v) = σ g (to_linear_map v))

-- What should be now prove about it? 

/-

## Categories

A category is a collection of objects, and between any pair of objects there's a collection
of maps or morphisms. Technical point: these maps/morphisms *don't actually have to be functions*,
the definition is more abstract than that. But let's not dwell on this right now.

That's not the end of the definition of a category -- there is a bit more structure, 
and some axioms, but let's just give some examples first:

Example: in set theory the collection of all sets is a category; the morphisms between two sets
are just the functions between the sets. 

Example: In type theory the collection of all types is a category; the morphisms are again just
the functions between the types. 

Example: if we fix a field `k` and a group `G` then we can make a category whose objects
are `k`-vector spaces equipped with an action of `G` (i.e. representations of `G`) and
whose morphisms are the `G`-linear maps. Note that here the morphisms are *certain* maps
between the objects, but not *all* the maps.

Let's get back to the definition of a category. I need to explain the extra
structure and the axioms of a category. The extra structure is:

S1) For every object `X` of the category, there has to be an identity morphism `id_X : X → X`
S2) If we have three objects `X`, `Y`, and `Z` in the category, and two morphisms
`f : X → Y` and `g : Y → Z` then there's a way of composing them to get `g ∘ f : X → Z`.

For example, in the representation theory example above, the category theoretic composition
is just defined to be function composition, and ensuring that this gives a valid morphism
boils down to checking that the composite of two `G`-linear maps is `G`-linear. 

The axioms are:

A1) If `f : X → Y` then `id_Y ∘ f = f` and `f ∘ id_X = f`
A2) If `f : W → X`, `g : X → Y` and `h : Y → Z` then `(f ∘ g) ∘ h = f ∘ (g ∘ h)`

The reason I mention these is that they inform us about what we should be proving
about `rep_map`!

-/

namespace rep_map

def id (ρ : representation k G V) : rep_map ρ ρ := 
{ to_linear_map := linear_map.id,
  map_apply := sorry }

variables {X : Type} [add_comm_group X] [module k X]

variables {ρ σ}

def comp {τ : representation k G X}
  (ψ : rep_map σ τ) (φ : rep_map ρ σ) : rep_map ρ τ :=
{ to_linear_map := ψ.to_linear_map.comp φ.to_linear_map,
  map_apply := sorry }

lemma comp_id (φ : rep_map ρ σ) : φ.comp (id ρ) = φ :=
begin
  sorry
end

lemma id_comp (φ : rep_map ρ σ) : (id σ).comp φ = φ :=
begin
  sorry
end

lemma comp_assoc {τ : representation k G X} {Y : Type} [add_comm_group Y] [module k Y]
  {υ : representation k G Y} (ξ : rep_map τ υ) (ψ : rep_map σ τ) (φ : rep_map ρ σ) : 
  (ξ.comp ψ).comp φ = ξ.comp (ψ.comp φ) := 
begin
  sorry
end

end rep_map
