/-
Copyright (c) 2023 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author : Kevin Buzzard
-/

import field_theory.abel_ruffini

/-

## Insolvability of the quintic

There exist polynomials whose solutions cannot be expressed by radicals.

Let `E` be a field and assume `p : E[X]` is a polynomial 
-/

open_locale polynomial

variables (E : Type) [field E] (p : E[X])

-- The Galois group of `p` is the Galois group of `F/E` where `F` is the splitting field of `p`.

open polynomial

example : p.gal = ((splitting_field p) ≃ₐ[E] (splitting_field p)) := rfl

/- 
If F/E is any field extension at all, then `solvable_by_rad E F` is the intermediate field consisting
of elements which can be built using n'th roots and the field operations, starting from `E`. Here
is the rather beautiful definition of the underlying set of this intermediate field:

```
/-- Inductive definition of solvable by radicals -/
inductive is_solvable_by_rad : E → Prop
| base (a : F) : is_solvable_by_rad (algebra_map F E a)
| add (a b : E) : is_solvable_by_rad a → is_solvable_by_rad b → is_solvable_by_rad (a + b)
| neg (α : E) : is_solvable_by_rad α → is_solvable_by_rad (-α)
| mul (α β : E) : is_solvable_by_rad α → is_solvable_by_rad β → is_solvable_by_rad (α * β)
| inv (α : E) : is_solvable_by_rad α → is_solvable_by_rad α⁻¹
| rad (α : E) (n : ℕ) (hn : n ≠ 0) : is_solvable_by_rad (α^n) → is_solvable_by_rad α
``` 

-/

variables  (F : Type) [field F] [algebra E F]
example : intermediate_field E F := solvable_by_rad E F 

-- The Abel-Ruffini theorem is that the min poly of an element in `solvable_by_rad E F` has solvable Galois group

example (a : solvable_by_rad E F) : is_solvable ((minpoly E a).gal) := solvable_by_rad.is_solvable a 

-- This was hard won! It was only finished a year or so ago.

-- A symmetric group of size 5 or more is known not to be solvable:

example (X : Type) (hX : 5 ≤ cardinal.mk X) : ¬is_solvable (equiv.perm X) := equiv.perm.not_solvable X hX 

-- Using a root of x^5-4x+2 and the machinery in this section, Browning proves

example : ∃ x : ℂ, is_algebraic ℚ x ∧ ¬ is_solvable_by_rad ℚ x := sorry

-- See the file `archive.100-theorems-list.16_abel_ruffini`. 

