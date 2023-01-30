/-
Copyright (c) 2022 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author : Kevin Buzzard
-/

import tactic -- imports all the Lean tactics
import group_theory.subgroup.basic -- import Lean's subgroups

/-

# Group homomorphisms

mathlib has group homomorphisms. The type of group homomorphisms from `G` to `H` is called
`monoid_hom G H`, but we hardly ever use that name; instead we use the notation, which
is `G →* H`, i.e. "`*`-preserving map between groups". Note in particular that we do *not* 
write `f : G → H` for a group homomorphism and then have some
function `is_group_hom : (G → H) → Prop` saying that it's a group homomorphism, we just have a
completely new type, whose terms are pairs consisting of the function and the axiom
that `f(g₁g₂)=f(g₁)f(g₂)` for all g₁ and g₂.
-/

-- Let `G` and `H` be groups.
variables {G H : Type} [group G] [group H]

-- let `φ : G → H` be a group homomorphism
variable (φ : G →* H)

-- Even though `φ` is not technically a function (it's a pair consisting of a function and
-- a proof), we can still evaluate `φ` at a term of type `G` and get a term of type `H`.

-- let `a` be an element of G
variable (a : G)

-- let's make the element `φ(a)` of `H`
example : H := φ a

-- If you use this in a proof, you'll see that actually this is denoted `⇑φ g`; what this
-- means is that `φ` is not itself a function, but there is a coercion from `G →* H`
-- to `G → H` sending `φ` to the underlying function from `G` to `H` (so, it forgets the
-- fact that φ is a group homomorphism and just remembers the function bit.

-- Here's the basic API for group homomorphisms

example (a b : G) : φ (a * b) = φ a * φ b := φ.map_mul a b
example : φ 1 = 1 := φ.map_one
example (a : G) : φ (a⁻¹) = (φ a)⁻¹ := φ.map_inv a

-- The identity group homomorphism from `G` to `G` is called `monoid_hom.id G`

example : monoid_hom.id G a = a :=
begin
  refl, -- true by definition
end

-- Let K be a third group.
variables (K : Type) [group K]

-- Let `ψ : H →* K` be another group homomorphism
variable (ψ : H →* K)

-- The composite of ψ and φ can't be written `ψ ∘ φ` in Lean, because `∘` is notation
-- for function composition, and `φ` and `ψ` aren't functions, they're collections of
-- data containing a function and some other things. So we use `monoid_hom.comp` to
-- compose functions. We can use dot notation for this.

example : G →* K := ψ.comp φ

-- When are two group homomorphisms equal? When they agree on all inputs. The `ext` tactic
-- knows this. 

-- The next three lemmas are pretty standard, but they are also in fact
-- the axioms that show that groups form a category.

lemma comp_id : φ.comp (monoid_hom.id G) = φ :=
begin
  ext x,
  refl,
end

lemma id_comp : (monoid_hom.id H).comp φ = φ :=
begin
  ext x,
  refl,
end

lemma comp_assoc {L : Type} [group L] (ρ : K →* L) :
  (ρ.comp ψ).comp φ = ρ.comp (ψ.comp φ) :=
begin
  refl,
end

-- The kernel of a group homomorphism `φ` is a subgroup of the source group.
-- The elements of the kernel are *defined* to be `{x | φ x = 1}`.
-- Note the use of dot notation to save us having to write `monoid_hom.ker`.
-- `φ.ker` *means* `monoid_hom.ker φ` because `φ` has type `monoid_hom [something]`

example (φ : G →* H) : subgroup G := φ.ker -- or `monoid_hom.ker φ`

example (φ : G →* H)  (x : G) : x ∈ φ.ker ↔ φ x = 1 :=
begin
  refl -- true by definition
end

-- Similarly the image is defined in the obvious way, with `monoid_hom.range`

example (φ : G →* H) : subgroup H := φ.range

example (φ : G →* H) (y : H) : y ∈ φ.range ↔ ∃ x : G, φ x = y :=
begin
  refl -- true by definition
end

-- `subgroup.map` is used for the image of a subgroup under a group hom

example (φ : G →* H) (S : subgroup G) : subgroup H := S.map φ

example (φ : G →* H) (S : subgroup G) (y : H) : y ∈ S.map φ ↔ ∃ x, x ∈ S ∧ φ x = y :=
begin
  refl,
end

-- and `subgroup.comap` is used for the preimage of a subgroup under a group hom.

example (φ : G →* H) (S : subgroup H) : subgroup G := S.comap φ

example (φ : G →* H) (T : subgroup H) (x : G) : x ∈ T.comap φ ↔ φ x ∈ T :=
begin
  refl,
end

-- Here are some basic facts about these constructions.

-- Preimage of a subgroup along the identity map is the same subgroup
example (S : subgroup G) : S.comap (monoid_hom.id G) = S :=
begin
  ext x,
  refl,
end

-- Image of a subgroup along the identity map is the same subgroup
example (S : subgroup G) : S.map (monoid_hom.id G) = S :=
begin
  ext x,
  split,
  { rintro ⟨y, hy, rfl⟩,
    exact hy, },
  { intro hx,
    exact ⟨x, hx, rfl⟩, },
end

-- preimage preserves `≤` (i.e. if `S ≤ T` are subgroups of `H` then `φ⁻¹(S) ≤ φ⁻¹(T)`)
example (φ : G →* H) (S T : subgroup H) (hST : S ≤ T) : S.comap φ ≤ T.comap φ :=
begin
  intros g hg,
  apply hST,
  exact hg,
end

-- image preserves `≤` (i.e. if `S ≤ T` are subgroups of `G` then `φ(S) ≤ φ(T)`)
example (φ : G →* H) (S T : subgroup G) (hST : S ≤ T) : S.map φ ≤ T.map φ :=
begin
  rintros h ⟨g, hg, rfl⟩,
  refine ⟨g, _, rfl⟩,
  exact hST hg,
end

-- Pulling a subgroup back along one homomorphism and then another, is equal
-- to pulling it back along the composite of the homomorphisms.
example (φ : G →* H) (ψ : H →* K) (U : subgroup K) :
  U.comap (ψ.comp φ) = (U.comap ψ).comap φ := 
begin
  refl,
end

-- Pushing a subgroup along one homomorphism and then another is equal to
--  pushing it forward along the composite of the homomorphisms.
example (φ : G →* H) (ψ : H →* K) (S : subgroup G) :
  S.map (ψ.comp φ) = (S.map φ).map ψ := 
begin
  ext c,
  split,
  { rintro ⟨a, ha, rfl⟩,
    refine ⟨φ a, _, rfl⟩,
    exact ⟨a, ha, rfl⟩, }, 
  { rintro ⟨b, ⟨a, ha, rfl⟩, rfl⟩,
    exact ⟨a, ha, rfl⟩, },
end

