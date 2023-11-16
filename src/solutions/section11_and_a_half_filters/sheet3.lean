/-
Copyright (c) 2023 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author : Kevin Buzzard
-/

import tactic -- imports all the Lean tactics
import order.filter.basic

/-!

# Examples of filters

## `at_top` filter on a totally ordered set

Let `L` be a non-empty totally ordered set. Let's say that a subset `X` of `L` is
"big" if there exists `x : L` such for all `y ≥ x`, `y ∈ X`.

I claim that the big subsets are a filter. Check this. The mathematical idea
is that the "big subsets" are the neighbourhoods of `∞`, so the corresponding
filter is some representation of an infinitesimal neighbourhood of `∞`.

Implementation notes: `linear_order L` is the type of linear orders on `L`.
`e : L` is just an easy way of saying that `L` is nonempty.

Recall that `max x y` is the max of x and y in a `linear_order`, and
`le_max_left a b : a ≤ max a b` and similarly `le_max_right`. 
-/

open set

def at_top (L : Type) [linear_order L] (e : L) : filter L :=
{ sets := {X : set L | ∃ x : L, ∀ y, x ≤ y → y ∈ X},
  univ_sets := begin
    use e,
    intros y hy,
    exact mem_univ y,    
  end,
  sets_of_superset := begin
    rintros X Y ⟨x, hX⟩ hXY,
    --rw mem_set_of_eq,
    use x,
    intros y hxy,
    --rw subset_def at hXY,
    apply hXY,
    exact hX _ hxy,
  end,
  inter_sets := begin
    rintros X Y ⟨x, hX⟩ ⟨y, hY⟩,
    use max x y,
    intros z hz,
    split,
    { apply hX, 
      apply le_trans _ hz,
      exact le_max_left x y },
    { exact hY _ (le_trans (le_max_right _ _) hz) }
  end }

/-
 
## the cofinite filter

The _cofinite filter_ on a type `α` has as its sets the subsets `S : set α`
with the property that `Sᶜ`, the complement of `S`, is finite.
Let's show that these are a filter.

Things you might find helpful:

`compl_univ : univᶜ = ∅`
`finite_empty : finite ∅`
`compl_subset_compl : Xᶜ ⊆ Yᶜ ↔ Y ⊆ X`
`finite.subset : S.finite → ∀ {T : set α}, T ⊆ S → T.finite`
`compl_inter S T : (S ∩ T)ᶜ = Sᶜ ∪ Tᶜ`
`finite.union : S.finite → T.finite → (S ∪ T).finite`

NB if you are thinking "I could never use Lean by myself, I don't know
the names of all the lemmas so I have to rely on Kevin telling them all to
me" then what you don't realise is that I myself don't know the names
of all the lemmas either -- I am literally just guessing them and pressing
ctrl-space to check. Look at the names of the lemmas and begin to understand
that you can probably guess them yourself.
-/

def cofinite (α : Type) : filter α :=
{ sets := { S : set α | (Sᶜ).finite },
  univ_sets := begin
    rw mem_set_of_eq,
    rw compl_univ,
    exact finite_empty,
  end,
  sets_of_superset := begin
    intros S T hS hST,
    rw mem_set_of_eq at hS ⊢,
    rw ← compl_subset_compl at hST,
    exact finite.subset hS hST,
  end,
  inter_sets := begin
    intros S T hS hT,
    rw mem_set_of_eq at *,
    rw compl_inter,
    exact finite.union hS hT,
  end }

/-

## Harder exercises.

If you like this filter stuff, then formalise in Lean and prove the following:

(1) prove that the cofinite filter on a finite type is the entire power set filter (`⊥`).
(2) prove that the cofinite filter on `ℕ` is equal to the `at_top` filter.
(3) Prove that the cofinite filter on `ℤ` is not equal to the `at_top` filter.
(4) Prove that the cofinite filter on `ℕ` is not principal.

-/

