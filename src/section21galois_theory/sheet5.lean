/-
Copyright (c) 2023 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author : Kevin Buzzard
-/

import field_theory.galois
/-

# Galois extensions

An extension is Galois if it's algebraic, normal and separable (note that both
normal and separable imply algebraic in Lean).

-/

variables (E F : Type) [field E] [field F] [algebra E F] [is_galois E F]

/-

The Galois group Gal(F/E) doesn't have special notation, it's just the F-algebra isomorphisms
from E to itself

-/

example : Type := F ≃ₐ[E] F

-- It's a group

example : group (F ≃ₐ[E] F) := infer_instance

-- If F/E is furthermore finite-dimensional then its dimension is the size of the group.

open finite_dimensional

example [finite_dimensional E F] : fintype.card (F ≃ₐ[E] F) = finrank E F :=
is_galois.card_aut_eq_finrank E F 

-- The fundamental theorem of Galois theory for finite Galois extensions
-- is an order-reversing bijection between subgroups of the Galois group 
-- and intermediate fields of the field extension. Here are the maps:

example : subgroup (F ≃ₐ[E] F) → intermediate_field E F := intermediate_field.fixed_field
example : intermediate_field E F → subgroup (F ≃ₐ[E] F) := intermediate_field.fixing_subgroup

open intermediate_field

variable [finite_dimensional E F]

-- They're inverse bijections
example (H : subgroup (F ≃ₐ[E] F)) : fixing_subgroup (fixed_field H) = H := fixing_subgroup_fixed_field H
example (L : intermediate_field E F) : fixed_field (fixing_subgroup L) = L := is_galois.fixed_field_fixing_subgroup L
-- weirdly, one of those is in the `is_galois` namespace and the other isn't. 

-- In the finite Galois case, this can be summarised as follows (≃o is order-preserving bijection; ᵒᵈ is "same set but reverse the order")
example : intermediate_field E F ≃o (subgroup (F ≃ₐ[E] F))ᵒᵈ := is_galois.intermediate_field_equiv_subgroup

-- I don't know if we have the result that the subgroup `H` is normal iff the subfield `L` is normal over `E`.

-- The results described above and the techniques used to prove them are described in this 2021 paper
-- by Browning and Lutz : https://arxiv.org/abs/2107.10988

