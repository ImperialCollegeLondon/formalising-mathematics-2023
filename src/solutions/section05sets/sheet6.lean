/-
Copyright (c) 2022 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author : Kevin Buzzard
-/

import tactic -- imports all the Lean tactics
import data.real.basic -- the reals

/-!

# Sets in Lean, sheet 6 : pushforward and pullback

## Pushforward of a set along a map

If `f : X → Y` then given a subset `S : set X` of `X` we can push it
forward to make a subset `f(S) : set Y` of `Y`. The definition
of `f(S)` is `{y : Y | ∃ x : X, x ∈ S ∧ f x = y}`. 

However `f(S)` doesn't make sense in Lean, because `f` eats
terms of type `X` and not `S`, which has type `set X`. 
In Lean we use the notation `f '' S` for this. This is notation
for `set.image` and if you need any API for this, it's likely
to use the word `image`.

## Pullback of a set along a map

If `f : X → Y` then given a subset `T : set Y` of `Y` we can
pull it back to make a subset `f⁻¹(T) : set X` of `X`. The definition
of `f⁻¹(T)` is `{x : X | f x ∈ T}`.

However `f⁻¹(T)` doesn't make sense in Lean either, because
`⁻¹` is notation for `has_inv.inv`, whose type in Lean
is `α → α`. In other words, if `x` has a certain type, then
`x⁻¹` *must* have the same type. The notation was basically designed
for group theory. In Lean we use the notation `f ⁻¹' T` for this pullback.

-/

variables (X Y : Type) (f : X → Y) (S : set X) (T : set Y)

example : S ⊆ f ⁻¹' (f '' S) :=
begin
  intros x hx,
  exact ⟨x, hx, rfl⟩, -- use x, etc etc also works
end

example : f '' (f ⁻¹' T) ⊆ T :=
begin
  rintros _ ⟨x, hx, rfl⟩,
  exact hx,
end

example : f '' S ⊆ T ↔ S ⊆ f ⁻¹' T :=
begin
  split,
  { intros h x hxS,
    refine h ⟨x, hxS, rfl⟩ },
  { rintro h _ ⟨x, hx, rfl⟩,
    refine h hx }
end

-- Pushforward and pullback along the identity map don't change anything

-- pullback is not so hard
example : id ⁻¹' S = S :=
begin
  refl
end

-- pushforward is a little trickier. You might have to `ext x, split`.
example : id '' S = S :=
begin
  ext x,
  split,
  { rintro ⟨y, hyS, rfl⟩,
    exact hyS, },
  { intro hxS,
    use x,
    exact ⟨hxS, rfl⟩, },
end

-- Now let's try composition.
variables (Z : Type) (g : Y → Z) (U : set Z)

-- preimage of preimage is preimage of comp
example : (g ∘ f) ⁻¹' U = f ⁻¹' (g ⁻¹' U) :=
begin
  refl,
end

-- preimage of preimage is preimage of comp
example : (g ∘ f) '' S = g '' (f '' S) :=
begin
  ext x,
  split,
  { rintro ⟨x, hxS, rfl⟩,
    refine ⟨f x, _, rfl⟩,
    exact ⟨x, hxS, rfl⟩, },
  { rintro ⟨y, ⟨x, hxS, rfl⟩, rfl⟩,
    exact ⟨x, hxS, rfl⟩, },
end
