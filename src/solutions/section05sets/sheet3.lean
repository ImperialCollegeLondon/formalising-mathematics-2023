/-
Copyright (c) 2022 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author : Kevin Buzzard
-/

import tactic -- imports all the Lean tactics

/-!

# Sets in Lean, example sheet 3 : not in (`∉`) and complement `Aᶜ`

The definition in Lean of `x ∉ A` is `¬ (x ∈ A)`. In other words,
`x ∉ A`, `¬ (x ∈ A)` and `(x ∈ A) → false` are all equal *by definition*
in Lean. 

The complement of a subset `A` of `X` is the subset `Aᶜ`; it's the terms of
type `X` which aren't in `A`. The *definition* of `x ∈ Aᶜ` is `x ∉ A`. 

For example, if you have a hypothesis `h : x ∈ Aᶜ` and your goal
is `false`, then `apply h` will work and will change the goal to `x ∈ A`.
Think a bit about why.

-/

open set

variables
  (X : Type) -- Everything will be a subset of `X`
  (A B C D E : set X) -- A,B,C,D,E are subsets of `X`
  (x y z : X) -- x,y,z are elements of `X` or, more precisely, terms of type `X`

example : x ∉ A → (x ∈ A → false) :=
begin
  intro h,
  exact h,
end

example : x ∈ A → (x ∉ A → false) :=
begin
  intros h1 h2,
  exact h2 h1,
end

example : (A ⊆ B) → x ∉ B → x ∉ A :=
begin
  intros hAB hB hA,
  apply hB,
  exact hAB hA,
end

-- Lean couldn't work out what I meant when I wrote `x ∈ ∅` so I had
-- to give it a hint by telling it the type of `∅`.
example : x ∉ (∅ : set X):=
begin
  intro h,
  exact h,
end

example : x ∈ Aᶜ ↔ x ∉ A :=
begin
  refl,
end

example : (∀ x, x ∈ A) ↔ ¬ (∃ x, x ∈ Aᶜ) :=
begin
  -- `hint` tells you some tactics which do this in one line
  -- `simp`, `finish`, `tidy` all work and so do other things
  -- also `exact not_exists_not.symm` works
  -- And `library_search` works after
  -- `change (∀ x, x ∈ A) ↔ ¬ (∃ x, x ∉ A)`
  split,
  { rintros h1 ⟨x, hx⟩,
    exact hx (h1 x) },
  { intros h x,
    by_contra h2,
    apply h,
    exact ⟨x, h2⟩ },
end

example : (∃ x, x ∈ A) ↔ ¬ (∀ x, x ∈ Aᶜ) :=
begin
  finish,
end
